#!/usr/bin/env python3
"""
Cat's N64 (PJ64 0.1–inspired) — clean-slate Python frontend + minimal homebrew-only core.

This is NOT Project64 code and does not include any proprietary BIOS/PIF ROM.
It uses a small HLE boot that loads the ROM payload into RDRAM and jumps to the
ROM's entry point. Disk-backed saves are disabled ("files = off").

Compatibility target: very simple homebrew that:
  - runs on the R4300i without FPU/TLB requirements
  - uses framebuffer output via VI registers (RGBA5551 / RGBA8888)
  - optionally uses PI DMA to stream data from cartridge ROM into RDRAM

Limitations (by design in this clean-slate 0.1):
  - No RSP (vector unit) emulation, no RDP display lists, no audio, no controllers
  - No TLB / exceptions / most interrupts
  - Interpreter-only (slow), meant for learning + bootstrapping

If you want to grow it into "real PJ64-like" compatibility, the next big chunks are:
  RSP, RDP, CPU exceptions/interrupts, timing, SI/controller, AI/audio, and TLB.
"""

from __future__ import annotations

import struct
import threading
import queue
import time
import tkinter as tk
from dataclasses import dataclass
from tkinter import ttk, filedialog, messagebox
from typing import Optional, Tuple

try:
    from PIL import Image, ImageTk  # type: ignore
    _HAVE_PIL = True
except Exception:
    _HAVE_PIL = False


# ----------------------------
# Utilities (endianness, ints)
# ----------------------------

U64_MASK = 0xFFFFFFFFFFFFFFFF
U32_MASK = 0xFFFFFFFF


def u64(x: int) -> int:
    return x & U64_MASK


def u32(x: int) -> int:
    return x & U32_MASK


def s16(x: int) -> int:
    x &= 0xFFFF
    return x - 0x10000 if (x & 0x8000) else x


def s32(x: int) -> int:
    x &= 0xFFFFFFFF
    return x - 0x100000000 if (x & 0x80000000) else x


def sext32_to_64(x: int) -> int:
    """Sign-extend 32-bit to 64-bit (stored as Python int masked to u64)."""
    return u64(s32(x))


def zext32_to_64(x: int) -> int:
    return u64(u32(x))


def clamp(v: int, lo: int, hi: int) -> int:
    return lo if v < lo else hi if v > hi else v


# ----------------------------
# ROM loading (z64/v64/n64)
# ----------------------------

@dataclass
class RomImage:
    data_be: bytes          # big-endian word order (z64-style)
    name: str
    entry_point: int        # virtual address from header
    size: int

    @staticmethod
    def from_file(path: str) -> "RomImage":
        raw = open(path, "rb").read()
        if len(raw) < 0x40:
            raise ValueError("ROM too small")

        # N64 ROM "magic" varies by byte order.
        magic = raw[:4]
        if magic == b"\x80\x37\x12\x40":
            be = raw  # z64
        elif magic == b"\x37\x80\x40\x12":
            # v64: swap each 16-bit halfword
            b = bytearray(raw)
            for i in range(0, len(b), 2):
                if i + 1 < len(b):
                    b[i], b[i + 1] = b[i + 1], b[i]
            be = bytes(b)
        elif magic == b"\x40\x12\x37\x80":
            # n64: little-endian words -> big-endian words
            b = bytearray(raw)
            for i in range(0, len(b), 4):
                if i + 3 < len(b):
                    b[i:i+4] = b[i:i+4][::-1]
            be = bytes(b)
        else:
            # Unknown: assume big-endian
            be = raw

        entry_point = struct.unpack(">I", be[0x08:0x0C])[0]
        name_bytes = be[0x20:0x34]  # 20 bytes internal name
        name = name_bytes.split(b"\x00", 1)[0].decode("ascii", errors="replace").strip()
        if not name:
            name = "Untitled ROM"

        return RomImage(data_be=be, name=name, entry_point=entry_point, size=len(be))


# ----------------------------
# Minimal VI (framebuffer output)
# ----------------------------

class VideoInterface:
    # Physical register base (RCP): 0x04400000 .. 0x044FFFFF
    VI_BASE = 0x04400000

    # Registers (offsets)
    VI_CONTROL = 0x00
    VI_ORIGIN  = 0x04
    VI_WIDTH   = 0x08

    def __init__(self, rdram: bytearray):
        self.rdram = rdram
        self.control = 0
        self.origin = 0
        self.width = 0

        # Heuristic default output size (until program sets VI regs)
        self.default_width = 320
        self.default_height = 240

    def mmio_read32(self, off: int) -> int:
        if off == self.VI_CONTROL:
            return self.control
        if off == self.VI_ORIGIN:
            return self.origin
        if off == self.VI_WIDTH:
            return self.width
        return 0

    def mmio_write32(self, off: int, val: int) -> None:
        val = u32(val)
        if off == self.VI_CONTROL:
            self.control = val
        elif off == self.VI_ORIGIN:
            # Origin is a physical address in RDRAM.
            self.origin = val & 0x00FFFFFF  # keep within 16MB-ish
        elif off == self.VI_WIDTH:
            self.width = val & 0x0FFF  # typical mask

    def _guess_dimensions(self) -> Tuple[int, int]:
        w = self.width if self.width else self.default_width
        # common heuristics
        if w <= 320:
            h = 240
        elif w <= 640:
            h = 480
        else:
            h = self.default_height
        return w, h

    def snapshot_rgb24(self) -> Optional[Tuple[int, int, bytes]]:
        """
        Convert framebuffer to RGB24 bytes.
        Returns (w, h, rgb_bytes) or None if VI isn't configured.
        """
        w, h = self._guess_dimensions()
        if w <= 0 or h <= 0:
            return None

        # VI_CONTROL type bits (very simplified):
        # 0 = blank/disabled, 2 = 16-bit, 3 = 32-bit
        fmt = self.control & 0x3
        if fmt == 0:
            return None

        start = self.origin
        rdram_len = len(self.rdram)

        if fmt == 2:
            # RGBA5551, 2 bytes per pixel
            needed = w * h * 2
            if start + needed > rdram_len:
                return None
            src = self.rdram[start:start+needed]
            out = bytearray(w * h * 3)
            j = 0
            for i in range(0, len(src), 2):
                v = (src[i] << 8) | src[i+1]
                r5 = (v >> 11) & 0x1F
                g5 = (v >> 6) & 0x1F
                b5 = (v >> 1) & 0x1F
                out[j]   = (r5 * 255) // 31
                out[j+1] = (g5 * 255) // 31
                out[j+2] = (b5 * 255) // 31
                j += 3
            return w, h, bytes(out)

        if fmt == 3:
            # RGBA8888, 4 bytes per pixel (assume big-endian R,G,B,A)
            needed = w * h * 4
            if start + needed > rdram_len:
                return None
            src = self.rdram[start:start+needed]
            out = bytearray(w * h * 3)
            j = 0
            for i in range(0, len(src), 4):
                out[j]   = src[i]
                out[j+1] = src[i+1]
                out[j+2] = src[i+2]
                j += 3
            return w, h, bytes(out)

        return None


# ----------------------------
# Minimal PI (DMA from cart ROM)
# ----------------------------

class PeripheralInterface:
    PI_BASE = 0x04600000

    PI_DRAM_ADDR = 0x00
    PI_CART_ADDR = 0x04
    PI_RD_LEN    = 0x08
    PI_WR_LEN    = 0x0C
    PI_STATUS    = 0x10

    def __init__(self, rdram: bytearray, cart_rom: bytes):
        self.rdram = rdram
        self.cart_rom = cart_rom

        self.dram_addr = 0
        self.cart_addr = 0
        self.status = 0  # bit0 busy (simplified)

    def mmio_read32(self, off: int) -> int:
        if off == self.PI_DRAM_ADDR:
            return self.dram_addr
        if off == self.PI_CART_ADDR:
            return self.cart_addr
        if off == self.PI_STATUS:
            return self.status
        return 0

    def mmio_write32(self, off: int, val: int) -> None:
        val = u32(val)
        if off == self.PI_DRAM_ADDR:
            self.dram_addr = val & 0x00FFFFFF
        elif off == self.PI_CART_ADDR:
            # cart address is physical, often in 0x1000_0000 domain
            self.cart_addr = val & 0x1FFFFFFF
        elif off == self.PI_RD_LEN:
            self._dma_cart_to_rdram(length=(val & 0x00FFFFFF) + 1)
        elif off == self.PI_WR_LEN:
            self._dma_rdram_to_cart(length=(val & 0x00FFFFFF) + 1)
        elif off == self.PI_STATUS:
            # writing can clear interrupts on real hw; here we just allow clearing busy
            self.status &= ~1

    def _dma_cart_to_rdram(self, length: int) -> None:
        self.status |= 1  # busy
        dram = self.dram_addr
        cart = self.cart_addr

        # In practice, cart is often 0x10000000+offset; our physical map provides that.
        # Map physical cart region 0x10000000.. to ROM offset 0.
        if cart >= 0x10000000:
            cart_off = cart - 0x10000000
        else:
            cart_off = cart  # permissive

        cart_end = clamp(cart_off + length, 0, len(self.cart_rom))
        dram_end = clamp(dram + (cart_end - cart_off), 0, len(self.rdram))
        n = max(0, dram_end - dram)
        if n > 0 and cart_off + n <= len(self.cart_rom):
            self.rdram[dram:dram+n] = self.cart_rom[cart_off:cart_off+n]

        self.status &= ~1  # done

    def _dma_rdram_to_cart(self, length: int) -> None:
        # "files=off": don't emulate writable cart (SRAM/Flash). Ignore safely.
        self.status |= 1
        self.status &= ~1


# ----------------------------
# Memory bus (very partial)
# ----------------------------

class MemoryBus:
    def __init__(self, rdram_size: int = 8 * 1024 * 1024):
        self.rdram = bytearray(rdram_size)
        self.sp_dmem = bytearray(0x1000)
        self.sp_imem = bytearray(0x1000)

        self.rom: bytes = b""
        self.vi = VideoInterface(self.rdram)
        self.pi = PeripheralInterface(self.rdram, self.rom)

    def attach_rom(self, rom_be: bytes) -> None:
        self.rom = rom_be
        self.pi = PeripheralInterface(self.rdram, self.rom)

    @staticmethod
    def va_to_pa(addr: int) -> int:
        addr = u64(addr)
        # Direct-mapped segments: KSEG0/KSEG1 => physical lower 29 bits.
        if 0x80000000 <= addr <= 0xBFFFFFFF:
            return int(addr & 0x1FFFFFFF)
        return int(addr & 0xFFFFFFFF)  # permissive fallback

    def _read_byte_phys(self, paddr: int) -> int:
        # RDRAM (0x00000000 ..)
        if 0 <= paddr < len(self.rdram):
            return self.rdram[paddr]

        # SP DMEM
        if 0x04000000 <= paddr <= 0x04000FFF:
            return self.sp_dmem[paddr - 0x04000000]

        # SP IMEM
        if 0x04001000 <= paddr <= 0x04001FFF:
            return self.sp_imem[paddr - 0x04001000]

        # Cartridge ROM (Domain 1 Address 2)
        if 0x10000000 <= paddr < 0x10000000 + len(self.rom):
            return self.rom[paddr - 0x10000000]

        # Open bus
        return 0

    def _write_byte_phys(self, paddr: int, val: int) -> None:
        val &= 0xFF
        if 0 <= paddr < len(self.rdram):
            self.rdram[paddr] = val
            return

        if 0x04000000 <= paddr <= 0x04000FFF:
            self.sp_dmem[paddr - 0x04000000] = val
            return

        if 0x04001000 <= paddr <= 0x04001FFF:
            self.sp_imem[paddr - 0x04001000] = val
            return

        # writes to ROM ignored

    def read_u8(self, vaddr: int) -> int:
        paddr = self.va_to_pa(vaddr)

        # MMIO 32-bit windows: we allow byte reads by reading the aligned u32 and shifting.
        if 0x04400000 <= paddr <= 0x044FFFFF:
            aligned = paddr & ~3
            word = self.read_u32(aligned)
            shift = (3 - (paddr & 3)) * 8
            return (word >> shift) & 0xFF

        if 0x04600000 <= paddr <= 0x046FFFFF:
            aligned = paddr & ~3
            word = self.read_u32(aligned)
            shift = (3 - (paddr & 3)) * 8
            return (word >> shift) & 0xFF

        return self._read_byte_phys(paddr)

    def write_u8(self, vaddr: int, val: int) -> None:
        paddr = self.va_to_pa(vaddr)

        if 0x04400000 <= paddr <= 0x044FFFFF:
            aligned = paddr & ~3
            cur = self.read_u32(aligned)
            shift = (3 - (paddr & 3)) * 8
            mask = 0xFF << shift
            new = (cur & ~mask) | ((val & 0xFF) << shift)
            self.write_u32(aligned, new)
            return

        if 0x04600000 <= paddr <= 0x046FFFFF:
            aligned = paddr & ~3
            cur = self.read_u32(aligned)
            shift = (3 - (paddr & 3)) * 8
            mask = 0xFF << shift
            new = (cur & ~mask) | ((val & 0xFF) << shift)
            self.write_u32(aligned, new)
            return

        self._write_byte_phys(paddr, val)

    def read_u16(self, vaddr: int) -> int:
        b0 = self.read_u8(vaddr)
        b1 = self.read_u8(vaddr + 1)
        return (b0 << 8) | b1

    def write_u16(self, vaddr: int, val: int) -> None:
        self.write_u8(vaddr, (val >> 8) & 0xFF)
        self.write_u8(vaddr + 1, val & 0xFF)

    def read_u32(self, vaddr: int) -> int:
        paddr = self.va_to_pa(vaddr)

        # VI MMIO (aligned)
        if 0x04400000 <= paddr <= 0x0440FFFF:
            off = paddr - 0x04400000
            return u32(self.vi.mmio_read32(off))

        # PI MMIO (aligned)
        if 0x04600000 <= paddr <= 0x0460FFFF:
            off = paddr - 0x04600000
            return u32(self.pi.mmio_read32(off))

        b0 = self._read_byte_phys(paddr)
        b1 = self._read_byte_phys(paddr + 1)
        b2 = self._read_byte_phys(paddr + 2)
        b3 = self._read_byte_phys(paddr + 3)
        return (b0 << 24) | (b1 << 16) | (b2 << 8) | b3

    def write_u32(self, vaddr: int, val: int) -> None:
        paddr = self.va_to_pa(vaddr)
        val = u32(val)

        # VI MMIO (aligned)
        if 0x04400000 <= paddr <= 0x0440FFFF:
            off = paddr - 0x04400000
            self.vi.mmio_write32(off, val)
            return

        # PI MMIO (aligned)
        if 0x04600000 <= paddr <= 0x0460FFFF:
            off = paddr - 0x04600000
            self.pi.mmio_write32(off, val)
            return

        self._write_byte_phys(paddr, (val >> 24) & 0xFF)
        self._write_byte_phys(paddr + 1, (val >> 16) & 0xFF)
        self._write_byte_phys(paddr + 2, (val >> 8) & 0xFF)
        self._write_byte_phys(paddr + 3, val & 0xFF)


# ----------------------------
# R4300i (MIPS III-ish) interpreter (partial)
# ----------------------------

class CpuHalt(Exception):
    pass


class MipsCPU:
    def __init__(self) -> None:
        self.gpr = [0] * 32  # 64-bit regs
        self.hi = 0
        self.lo = 0
        self.pc = 0
        self.npc = 0

        # Minimal COP0 set (store as dict for readability)
        self.cp0 = {
            "Random": 0,
            "Status": 0,
            "Cause": 0,
            "EPC": 0,
            "PRId": 0,
            "Config": 0,
            "Count": 0,
            "Compare": 0,
        }

        self.instr_count = 0

    def reset_hle(self, entry_pc: int) -> None:
        # PIF ROM side-effects (HLE) — register initial state
        # (Values based on public documentation, not PJ64 code.)
        self.gpr = [0] * 32
        self.hi = 0
        self.lo = 0

        # GPR init (t3, s4, s6, sp)
        self.gpr[11] = u64(0xFFFFFFFFA4000040)  # t3
        self.gpr[20] = u64(0x1)                 # s4
        self.gpr[22] = u64(0x3F)                # s6
        self.gpr[29] = u64(0xFFFFFFFFA4001FF0)  # sp

        # COP0 init
        self.cp0["Random"] = 0x1F
        self.cp0["Status"] = 0x34000000
        self.cp0["PRId"] = 0x00000B00
        self.cp0["Config"] = 0x0006E463

        self.pc = u64(entry_pc)
        self.npc = u64(entry_pc + 4)
        self.instr_count = 0

    def _set_gpr(self, idx: int, val: int) -> None:
        if idx != 0:
            self.gpr[idx] = u64(val)

    def step(self, bus: MemoryBus) -> None:
        instr = bus.read_u32(self.pc)
        pc = self.pc
        npc = self.npc

        # Advance pipeline (MIPS delay-slot friendly model):
        self.pc = npc
        self.npc = u64(npc + 4)

        self.execute(instr, pc, npc, bus)
        self.gpr[0] = 0
        self.instr_count += 1

    def execute(self, instr: int, pc: int, npc: int, bus: MemoryBus) -> None:
        op = (instr >> 26) & 0x3F
        rs = (instr >> 21) & 0x1F
        rt = (instr >> 16) & 0x1F
        rd = (instr >> 11) & 0x1F
        sh = (instr >> 6) & 0x1F
        fn = instr & 0x3F
        imm = instr & 0xFFFF
        simm = s16(imm)
        target = instr & 0x03FFFFFF

        def branch(cond: bool) -> None:
            if cond:
                # branch target = (pc+4) + (offset<<2) ; npc == pc+4
                self.npc = u64(npc + (simm << 2))

        if op == 0x00:
            # SPECIAL
            if fn == 0x00:  # SLL
                self._set_gpr(rd, sext32_to_64(u32(self.gpr[rt] << sh)))
            elif fn == 0x02:  # SRL
                self._set_gpr(rd, sext32_to_64(u32(u32(self.gpr[rt]) >> sh)))
            elif fn == 0x03:  # SRA
                self._set_gpr(rd, sext32_to_64(u32(s32(u32(self.gpr[rt])) >> sh)))
            elif fn == 0x04:  # SLLV
                self._set_gpr(rd, sext32_to_64(u32(self.gpr[rt] << (self.gpr[rs] & 0x1F))))
            elif fn == 0x06:  # SRLV
                self._set_gpr(rd, sext32_to_64(u32(u32(self.gpr[rt]) >> (self.gpr[rs] & 0x1F))))
            elif fn == 0x07:  # SRAV
                self._set_gpr(rd, sext32_to_64(u32(s32(u32(self.gpr[rt])) >> (self.gpr[rs] & 0x1F))))
            elif fn == 0x08:  # JR
                self.npc = u64(self.gpr[rs])
            elif fn == 0x09:  # JALR
                link = u64(pc + 8)
                self._set_gpr(rd if rd != 0 else 31, link)
                self.npc = u64(self.gpr[rs])
            elif fn == 0x0C:  # SYSCALL
                raise CpuHalt("SYSCALL")
            elif fn == 0x0D:  # BREAK
                raise CpuHalt("BREAK")
            elif fn == 0x10:  # MFHI
                self._set_gpr(rd, self.hi)
            elif fn == 0x11:  # MTHI
                self.hi = u64(self.gpr[rs])
            elif fn == 0x12:  # MFLO
                self._set_gpr(rd, self.lo)
            elif fn == 0x13:  # MTLO
                self.lo = u64(self.gpr[rs])
            elif fn == 0x18:  # MULT
                a = s32(u32(self.gpr[rs]))
                b = s32(u32(self.gpr[rt]))
                prod = a * b
                self.lo = u64(prod & U32_MASK)
                self.hi = u64((prod >> 32) & U32_MASK)
            elif fn == 0x19:  # MULTU
                a = u32(self.gpr[rs])
                b = u32(self.gpr[rt])
                prod = a * b
                self.lo = u64(prod & U32_MASK)
                self.hi = u64((prod >> 32) & U32_MASK)
            elif fn == 0x1A:  # DIV
                a = s32(u32(self.gpr[rs]))
                b = s32(u32(self.gpr[rt]))
                if b != 0:
                    self.lo = sext32_to_64(int(a / b))
                    self.hi = sext32_to_64(int(a % b))
            elif fn == 0x1B:  # DIVU
                a = u32(self.gpr[rs])
                b = u32(self.gpr[rt])
                if b != 0:
                    self.lo = zext32_to_64(a // b)
                    self.hi = zext32_to_64(a % b)
            elif fn == 0x20:  # ADD
                self._set_gpr(rd, sext32_to_64(u32(s32(u32(self.gpr[rs])) + s32(u32(self.gpr[rt])))))
            elif fn == 0x21:  # ADDU
                self._set_gpr(rd, sext32_to_64(u32(u32(self.gpr[rs]) + u32(self.gpr[rt]))))
            elif fn == 0x22:  # SUB
                self._set_gpr(rd, sext32_to_64(u32(s32(u32(self.gpr[rs])) - s32(u32(self.gpr[rt])))))
            elif fn == 0x23:  # SUBU
                self._set_gpr(rd, sext32_to_64(u32(u32(self.gpr[rs]) - u32(self.gpr[rt]))))
            elif fn == 0x24:  # AND
                self._set_gpr(rd, u64(self.gpr[rs] & self.gpr[rt]))
            elif fn == 0x25:  # OR
                self._set_gpr(rd, u64(self.gpr[rs] | self.gpr[rt]))
            elif fn == 0x26:  # XOR
                self._set_gpr(rd, u64(self.gpr[rs] ^ self.gpr[rt]))
            elif fn == 0x27:  # NOR
                self._set_gpr(rd, u64(~(self.gpr[rs] | self.gpr[rt])))
            elif fn == 0x2A:  # SLT
                self._set_gpr(rd, 1 if s32(u32(self.gpr[rs])) < s32(u32(self.gpr[rt])) else 0)
            elif fn == 0x2B:  # SLTU
                self._set_gpr(rd, 1 if u32(self.gpr[rs]) < u32(self.gpr[rt]) else 0)
            elif fn == 0x2D:  # DADDU (64-bit add unsigned, no overflow)
                self._set_gpr(rd, u64(self.gpr[rs] + self.gpr[rt]))
            else:
                raise CpuHalt(f"Unimplemented SPECIAL fn=0x{fn:02X}")

        elif op == 0x02:  # J
            self.npc = u64((pc & 0xF0000000) | (target << 2))
        elif op == 0x03:  # JAL
            self._set_gpr(31, u64(pc + 8))
            self.npc = u64((pc & 0xF0000000) | (target << 2))

        elif op == 0x04:  # BEQ
            branch(self.gpr[rs] == self.gpr[rt])
        elif op == 0x05:  # BNE
            branch(self.gpr[rs] != self.gpr[rt])
        elif op == 0x06:  # BLEZ
            branch(s32(u32(self.gpr[rs])) <= 0)
        elif op == 0x07:  # BGTZ
            branch(s32(u32(self.gpr[rs])) > 0)

        elif op == 0x08:  # ADDI
            self._set_gpr(rt, sext32_to_64(u32(s32(u32(self.gpr[rs])) + simm)))
        elif op == 0x09:  # ADDIU
            self._set_gpr(rt, sext32_to_64(u32(u32(self.gpr[rs]) + (simm & 0xFFFFFFFF))))
        elif op == 0x0A:  # SLTI
            self._set_gpr(rt, 1 if s32(u32(self.gpr[rs])) < simm else 0)
        elif op == 0x0B:  # SLTIU
            self._set_gpr(rt, 1 if u32(self.gpr[rs]) < u32(simm) else 0)
        elif op == 0x0C:  # ANDI
            self._set_gpr(rt, u64(self.gpr[rs] & imm))
        elif op == 0x0D:  # ORI
            self._set_gpr(rt, u64(self.gpr[rs] | imm))
        elif op == 0x0E:  # XORI
            self._set_gpr(rt, u64(self.gpr[rs] ^ imm))
        elif op == 0x0F:  # LUI
            self._set_gpr(rt, sext32_to_64(u32(imm << 16)))

        elif op == 0x10:  # COP0 (very small subset: MFC0/MTC0/ERET)
            cop_rs = rs
            cop_rd = rd
            if cop_rs == 0x00:  # MFC0 rt <- cp0[rd]
                val = 0
                if cop_rd == 1:
                    val = self.cp0["Random"]
                elif cop_rd == 9:
                    val = self.cp0["Count"]
                elif cop_rd == 11:
                    val = self.cp0["Compare"]
                elif cop_rd == 12:
                    val = self.cp0["Status"]
                elif cop_rd == 13:
                    val = self.cp0["Cause"]
                elif cop_rd == 14:
                    val = self.cp0["EPC"]
                elif cop_rd == 15:
                    val = self.cp0["PRId"]
                elif cop_rd == 16:
                    val = self.cp0["Config"]
                self._set_gpr(rt, sext32_to_64(val))
            elif cop_rs == 0x04:  # MTC0 cp0[rd] <- rt (low 32)
                val = u32(self.gpr[rt])
                if cop_rd == 9:
                    self.cp0["Count"] = val
                elif cop_rd == 11:
                    self.cp0["Compare"] = val
                elif cop_rd == 12:
                    self.cp0["Status"] = val
                elif cop_rd == 13:
                    self.cp0["Cause"] = val
                elif cop_rd == 14:
                    self.cp0["EPC"] = val
            elif cop_rs == 0x10 and fn == 0x18:
                # ERET (approx): pc <- EPC
                epc = u64(self.cp0["EPC"])
                self.pc = epc
                self.npc = u64(epc + 4)
            else:
                raise CpuHalt(f"Unimplemented COP0 rs=0x{cop_rs:02X} rd=0x{cop_rd:02X} fn=0x{fn:02X}")

        elif op == 0x20:  # LB
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u8(addr)
            self._set_gpr(rt, sext32_to_64(s32(v if v < 0x80 else v - 0x100)))
        elif op == 0x24:  # LBU
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u8(addr)
            self._set_gpr(rt, u64(v))
        elif op == 0x21:  # LH
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u16(addr)
            v = v - 0x10000 if v & 0x8000 else v
            self._set_gpr(rt, sext32_to_64(v))
        elif op == 0x25:  # LHU
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u16(addr)
            self._set_gpr(rt, u64(v))
        elif op == 0x23:  # LW
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u32(addr)
            self._set_gpr(rt, sext32_to_64(v))
        elif op == 0x27:  # LWU
            addr = u64(self.gpr[rs] + simm)
            v = bus.read_u32(addr)
            self._set_gpr(rt, zext32_to_64(v))

        elif op == 0x28:  # SB
            addr = u64(self.gpr[rs] + simm)
            bus.write_u8(addr, u32(self.gpr[rt]) & 0xFF)
        elif op == 0x29:  # SH
            addr = u64(self.gpr[rs] + simm)
            bus.write_u16(addr, u32(self.gpr[rt]) & 0xFFFF)
        elif op == 0x2B:  # SW
            addr = u64(self.gpr[rs] + simm)
            bus.write_u32(addr, u32(self.gpr[rt]))

        else:
            raise CpuHalt(f"Unimplemented opcode op=0x{op:02X}")


# ----------------------------
# HLE boot (homebrew-friendly)
# ----------------------------

def hle_load_program_into_rdram(bus: MemoryBus, rom: RomImage) -> None:
    """
    Approximate the early boot's "load game payload" step:
      Copy ROM bytes *after* the first 0x1000 bytes (IPL3/bootcode area)
      into RDRAM at physical address 0x00000400.

    This matches common ROM layout assumptions used by toolchains and docs:
      - the checksum region starts after 0x1000
      - the usual entrypoint is 0x80000400 (RDRAM+0x400)
    """
    src_off = 0x1000
    dst = 0x00000400
    if len(rom.data_be) <= src_off:
        return
    payload = rom.data_be[src_off:]
    # Keep it bounded (avoid overflow)
    n = min(len(payload), len(bus.rdram) - dst)
    if n > 0:
        bus.rdram[dst:dst+n] = payload[:n]


# ----------------------------
# Core runner (threaded)
# ----------------------------

class CatsN64Core:
    def __init__(self) -> None:
        self.bus = MemoryBus()
        self.cpu = MipsCPU()
        self.rom: Optional[RomImage] = None

        self._thread: Optional[threading.Thread] = None
        self._stop_evt = threading.Event()
        self._pause_evt = threading.Event()

        self.frame_q: "queue.Queue[Tuple[int,int,bytes]]" = queue.Queue(maxsize=2)
        self.stats_q: "queue.Queue[Tuple[int,float]]" = queue.Queue(maxsize=4)

    def load_rom(self, rom: RomImage) -> None:
        self.rom = rom
        self.bus.attach_rom(rom.data_be)

    def reset(self) -> None:
        if not self.rom:
            return
        # HLE: load payload to RDRAM + init CPU regs + jump to entrypoint
        hle_load_program_into_rdram(self.bus, self.rom)
        entry = self.rom.entry_point or 0x80000400
        self.cpu.reset_hle(entry_pc=entry)

    def start(self) -> None:
        if self._thread and self._thread.is_alive():
            return
        if not self.rom:
            raise RuntimeError("No ROM loaded")
        self._stop_evt.clear()
        self._pause_evt.clear()
        self.reset()
        self._thread = threading.Thread(target=self._run_loop, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._stop_evt.set()

    def pause(self, paused: bool) -> None:
        if paused:
            self._pause_evt.set()
        else:
            self._pause_evt.clear()

    def _run_loop(self) -> None:
        last_frame = time.perf_counter()
        last_stats = time.perf_counter()
        instrs_since = 0

        try:
            while not self._stop_evt.is_set():
                if self._pause_evt.is_set():
                    time.sleep(0.01)
                    continue

                # Run a small slice of instructions (interpreter is slow)
                slice_instr = 5000
                for _ in range(slice_instr):
                    self.cpu.step(self.bus)
                instrs_since += slice_instr

                now = time.perf_counter()

                # Video ~30fps by default (lower to survive in Python)
                if now - last_frame >= 1.0 / 30.0:
                    snap = self.bus.vi.snapshot_rgb24()
                    if snap is not None:
                        try:
                            self.frame_q.put_nowait(snap)
                        except queue.Full:
                            pass
                    last_frame = now

                # Stats ~2Hz
                if now - last_stats >= 0.5:
                    ips = int(instrs_since / (now - last_stats))
                    try:
                        self.stats_q.put_nowait((ips, now))
                    except queue.Full:
                        pass
                    instrs_since = 0
                    last_stats = now

                # Yield a bit
                time.sleep(0.001)

        except CpuHalt as e:
            # Stop on halt and bubble message via stats queue (UI reads it)
            try:
                self.stats_q.put_nowait((-1, time.perf_counter()))
            except queue.Full:
                pass
        except Exception:
            try:
                self.stats_q.put_nowait((-2, time.perf_counter()))
            except queue.Full:
                pass


# ----------------------------
# GUI (PJ64-ish ROM browser + video window)
# ----------------------------

class VideoWindow(tk.Toplevel):
    def __init__(self, parent: tk.Tk, show_fps: bool = True):
        super().__init__(parent)
        self.title("Cat's N64 — Video")
        self.geometry("720x540")
        self.resizable(True, True)

        self.show_fps = show_fps
        self._imgtk = None  # keep reference
        self._last_dims = (0, 0)

        self.label = tk.Label(self, text="(No frame yet)")
        self.label.pack(fill="both", expand=True)

        self.fps_var = tk.StringVar(value="")
        self.fps_label = tk.Label(self, textvariable=self.fps_var, anchor="w")
        if self.show_fps:
            self.fps_label.pack(fill="x", side="bottom")

    def update_frame(self, w: int, h: int, rgb: bytes, ips: Optional[int] = None) -> None:
        # Render via PIL if available (much faster than PhotoImage.put)
        if _HAVE_PIL:
            img = Image.frombytes("RGB", (w, h), rgb)
            # Scale up a bit if tiny
            if w < 400:
                scale = 2
                img = img.resize((w * scale, h * scale), Image.NEAREST)
            self._imgtk = ImageTk.PhotoImage(img)
            self.label.configure(image=self._imgtk, text="")
        else:
            # Fallback: show a text hint instead of extremely slow pixel pushing
            self.label.configure(text=f"Frame {w}x{h} received (install pillow for video)")
        if ips is not None and self.show_fps:
            self.fps_var.set(f"Interpreter: ~{ips:,} instr/s")


class MewRicePlugin:
    """Configuration stub for UI parity with your original script."""
    def __init__(self):
        self.name = "MewRice Video 0"
        self.config = {
            "Resolution": "640x480",
            "Rice_Hacks": False,
            "Show_FPS": True
        }

    def configure(self, parent_window):
        config_win = tk.Toplevel(parent_window)
        config_win.title(f"Configure {self.name}")
        config_win.geometry("300x220")
        config_win.resizable(False, False)

        tk.Label(config_win, text="Rendering Options", font=("Segoe UI", 9, "bold")).pack(pady=5)

        frame_res = tk.Frame(config_win)
        frame_res.pack(fill='x', padx=10)
        tk.Label(frame_res, text="Window Preset:").pack(side='left')
        res_var = tk.StringVar(value=self.config["Resolution"])
        res_combo = ttk.Combobox(frame_res, textvariable=res_var,
                                 values=["640x480", "800x600", "1024x768", "1280x720"])
        res_combo.pack(side='right')

        var_hacks = tk.BooleanVar(value=self.config["Rice_Hacks"])
        tk.Checkbutton(config_win, text="Enable Rice Format Hacks (no-op)", variable=var_hacks).pack(anchor='w', padx=10, pady=5)

        var_fps = tk.BooleanVar(value=self.config["Show_FPS"])
        tk.Checkbutton(config_win, text="Show FPS / IPS", variable=var_fps).pack(anchor='w', padx=10)

        def save():
            self.config["Resolution"] = res_var.get()
            self.config["Rice_Hacks"] = var_hacks.get()
            self.config["Show_FPS"] = var_fps.get()
            messagebox.showinfo("MewRice 0", "Configuration Saved!")
            config_win.destroy()

        tk.Button(config_win, text="OK", command=save, width=10).pack(side='bottom', pady=10)


class CatsProject64App:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Cat's N64 (Clean-Slate) — PJ64 0.1-ish")
        self.root.geometry("760x520")

        self.bg_color = "#F0F0F0"
        self.root.configure(bg=self.bg_color)

        self.mewrice = MewRicePlugin()
        self.core = CatsN64Core()

        self.games: list[Tuple[str, str]] = []  # (display name, path)
        self.video_win: Optional[VideoWindow] = None

        self._paused = False
        self._last_ips: Optional[int] = None

        self._setup_menu()
        self._setup_gui()

        # UI update loop
        self.root.after(16, self._pump_emu_queues)

    def _setup_menu(self) -> None:
        menubar = tk.Menu(self.root)

        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open Homebrew ROM...", command=self.open_rom)
        # "files = off": disable directory scanning and disk-backed saves
        file_menu.add_command(label="ROM Directory... (disabled)", state="disabled")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        sys_menu = tk.Menu(menubar, tearoff=0)
        sys_menu.add_command(label="Run / Resume", command=self.run_resume)
        sys_menu.add_command(label="Pause", command=self.pause_toggle)
        sys_menu.add_command(label="Hard Reset", command=self.reset_system)
        sys_menu.add_separator()
        sys_menu.add_command(label="Stop", command=self.stop_system)
        menubar.add_cascade(label="System", menu=sys_menu)

        opt_menu = tk.Menu(menubar, tearoff=0)
        opt_menu.add_command(label="Configure Graphics Plugin...", command=lambda: self.mewrice.configure(self.root))
        opt_menu.add_separator()
        opt_menu.add_command(label="Settings (files=off)", command=self.open_settings)
        menubar.add_cascade(label="Options", menu=opt_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

    def _setup_gui(self) -> None:
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="📂 Open", command=self.open_rom, relief=tk.FLAT).pack(side=tk.LEFT, padx=2, pady=2)
        tk.Button(toolbar, text="▶ Run", command=self.run_resume, relief=tk.FLAT).pack(side=tk.LEFT, padx=2, pady=2)
        tk.Button(toolbar, text="⏸ Pause", command=self.pause_toggle, relief=tk.FLAT).pack(side=tk.LEFT, padx=2, pady=2)
        tk.Button(toolbar, text="⟲ Reset", command=self.reset_system, relief=tk.FLAT).pack(side=tk.LEFT, padx=2, pady=2)
        tk.Button(toolbar, text="⏹ Stop", command=self.stop_system, relief=tk.FLAT).pack(side=tk.LEFT, padx=2, pady=2)

        self.tree = ttk.Treeview(self.root, columns=("Filename", "Title", "Notes"), show='headings')
        self.tree.heading("Filename", text="ROM File")
        self.tree.heading("Title", text="Internal Name")
        self.tree.heading("Notes", text="Notes")
        self.tree.column("Filename", width=260)
        self.tree.column("Title", width=320)
        self.tree.column("Notes", width=150)
        self.tree.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        self.tree.bind("<Double-1>", self.on_double_click)

        self.status_var = tk.StringVar(value="Ready (homebrew-only core, files=off)")
        self.statusbar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.statusbar.pack(side=tk.BOTTOM, fill=tk.X)

    def open_rom(self) -> None:
        filename = filedialog.askopenfilename(filetypes=[("N64 ROMs", "*.z64 *.v64 *.n64 *.rom"), ("All Files", "*.*")])
        if not filename:
            return
        try:
            rom = RomImage.from_file(filename)
        except Exception as e:
            messagebox.showerror("ROM Load Error", str(e))
            return

        # List insert
        display_file = filename.split("/")[-1]
        self.tree.insert("", "end", values=(display_file, rom.name, "Homebrew (assumed)"))
        self.games.append((display_file, filename))

        # Load into core
        self.core.load_rom(rom)
        self.status_var.set(f"Loaded: {rom.name} | entry=0x{rom.entry_point:08X}")

        messagebox.showinfo(
            "Homebrew Notice",
            "This clean-slate core is intended for homebrew / dev ROMs you have rights to.\n"
            "It does not implement full N64 hardware and will not run most commercial games."
        )

        # Auto-run
        self.run_resume()

    def on_double_click(self, event) -> None:
        sel = self.tree.selection()
        if not sel:
            return
        item = sel[0]
        fname = self.tree.item(item, "values")[0]
        for disp, path in self.games:
            if disp == fname:
                try:
                    rom = RomImage.from_file(path)
                    self.core.load_rom(rom)
                    self.status_var.set(f"Loaded: {rom.name} | entry=0x{rom.entry_point:08X}")
                    self.run_resume()
                except Exception as e:
                    messagebox.showerror("ROM Load Error", str(e))
                return

    def _ensure_video_window(self) -> None:
        if self.video_win and self.video_win.winfo_exists():
            return
        self.video_win = VideoWindow(self.root, show_fps=bool(self.mewrice.config.get("Show_FPS", True)))
        # apply window preset roughly
        res = self.mewrice.config.get("Resolution", "640x480")
        try:
            w, h = res.lower().split("x")
            self.video_win.geometry(f"{int(w)}x{int(h)}")
        except Exception:
            pass

    def run_resume(self) -> None:
        if not self.core.rom:
            return
        self._ensure_video_window()
        try:
            self.core.start()
            self.core.pause(False)
            self._paused = False
            self.status_var.set("Running (interpreter)")
        except Exception as e:
            messagebox.showerror("Run Error", str(e))

    def pause_toggle(self) -> None:
        if not self.core.rom:
            return
        self._paused = not self._paused
        self.core.pause(self._paused)
        self.status_var.set("Paused" if self._paused else "Running (interpreter)")

    def reset_system(self) -> None:
        if not self.core.rom:
            return
        self.core.reset()
        self.status_var.set("Reset (HLE boot)")

    def stop_system(self) -> None:
        self.core.stop()
        self.status_var.set("Stopped")

    def open_settings(self) -> None:
        messagebox.showinfo(
            "Settings",
            "files = off:\n"
            "- No SRAM/EEPROM/Flash backed to disk\n"
            "- No directory scanning\n\n"
            "This 0.1 core is intentionally minimal."
        )

    def show_about(self) -> None:
        messagebox.showinfo(
            "About",
            "Cat's N64 (Clean-Slate)\n"
            "Version 0.1 (PJ64-style frontend + tiny homebrew core)\n\n"
            "No proprietary PIF/BIOS included.\n"
            "Interpreter-only; designed for learning + experimentation."
        )

    def _pump_emu_queues(self) -> None:
        # Frames
        if self.video_win and self.video_win.winfo_exists():
            try:
                while True:
                    w, h, rgb = self.core.frame_q.get_nowait()
                    self.video_win.update_frame(w, h, rgb, ips=self._last_ips)
            except queue.Empty:
                pass

        # Stats (IPS)
        try:
            while True:
                ips, _t = self.core.stats_q.get_nowait()
                if ips >= 0:
                    self._last_ips = ips
                elif ips == -1:
                    self.status_var.set("CPU Halt (SYSCALL/BREAK)")
                else:
                    self.status_var.set("Core Error (exception)")
        except queue.Empty:
            pass

        self.root.after(16, self._pump_emu_queues)


def main() -> None:
    root = tk.Tk()
    try:
        style = ttk.Style()
        style.theme_use("clam")
    except Exception:
        pass
    app = CatsProject64App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
