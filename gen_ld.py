#!/usr/bin/env python3
"""
mk_ld.py  –  Emit an Ibex linker script whose *only* differences from the
             reference are the two ORIGIN addresses.

Usage
-----
    ./mk_ld.py <core_num> <output_file>

Where  <core_num>  is an integer ≥ 1.

Rule
----
    ram   ORIGIN = 0x0010_0000 * core_num
    stack ORIGIN = 0x0013_0000 + 0x0010_0000 * (core_num - 1)

Every other byte of the original linker script is reproduced verbatim.
"""

import argparse
import re
import sys
from pathlib import Path

TEMPLATE = """/* Copyright lowRISC contributors.
   Licensed under the Apache License, Version 2.0, see LICENSE for details.
   SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH(riscv)

MEMORY
{
/* Change this if you'd like different sizes. Arty A7-100(35) has a maximum of 607.5KB(225KB)
   BRAM space. Configuration below is for maximum BRAM capacity with Artya A7-35 while letting
   CoreMark run (.vmem of 152.8KB).
*/
    ram         : ORIGIN = 0x00100000, LENGTH = 0x30000 /* 192 kB */
    stack       : ORIGIN = 0x00130000, LENGTH = 0xFF00  /* 32 kB */
}

/* Stack information variables */
_min_stack      = 0x2000;   /* 8K - minimum stack space to reserve */
_stack_len     = LENGTH(stack);
_stack_start   = ORIGIN(stack) + LENGTH(stack);

_entry_point = _vectors_start + 0x80;
ENTRY(_entry_point)

/* The tohost address is used by Spike for a magic "stop me now" message. This
   is set to equal SIM_CTRL_CTRL (see simple_system_regs.h), which has that
   effect in simple_system simulations. Note that it must be 8-byte aligned.

   We don't read data back from Spike, so fromhost is set to some dummy value:
   we place it just above the top of the stack.
 */
tohost   = 0x20008;
fromhost = _stack_start + 0x10;

SECTIONS
{
    .vectors :
    {
        . = ALIGN(4);
\t\t_vectors_start = .;
        KEEP(*(.vectors))
\t\t_vectors_end = .;
    } > ram

    .text : {
        . = ALIGN(4);
        *(.text)
        *(.text.*)
    }  > ram

    .rodata : {
        . = ALIGN(4);
        /* Small RO data before large RO data */
        *(.srodata)
        *(.srodata.*)
        *(.rodata);
        *(.rodata.*)
    } > ram

    .data : {
        . = ALIGN(4);
        /* Small data before large data */
        *(.sdata)
        *(.sdata.*)
        *(.data);
        *(.data.*)
    } > ram

    .bss :
    {
        . = ALIGN(4);
        _bss_start = .;
        /* Small BSS before large BSS */
        *(.sbss)
        *(.sbss.*)
        *(.bss)
        *(.bss.*)
        *(COMMON)
        _bss_end = .;
    } > ram

    /* ensure there is enough room for stack */
    .stack (NOLOAD): {
        . = ALIGN(4);
        . = . + _min_stack ;
        . = ALIGN(4);
        stack = . ;
        _stack = . ;
    } > stack
}"""


def hex8(val: int) -> str:
    """Return 32‑bit hex literal in 0xXXXXXXXX format (uppercase)."""
    return f"0x{val:08X}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("core", type=int, help="core number (≥1)")
    ap.add_argument("outfile", type=Path, help="output .ld filename")
    args = ap.parse_args()

    if args.core < 1:
        sys.exit("core must be ≥1")

    ram_origin   = 0x0010_0000 * (args.core)
    stack_origin = 0x0013_0000 + 0x0010_0000 * (args.core - 1)

    text = TEMPLATE
    # Replace only the two hex literals; preserve everything else byte‑for‑byte.
    text = re.sub(r"0x00100000", hex8(ram_origin),   text, count=1)
    text = re.sub(r"0x00130000", hex8(stack_origin), text, count=1)

    args.outfile.write_text(text)
    print(f"Generated linker script for core {args.core} -> {args.outfile}")


if __name__ == "__main__":
    main()
