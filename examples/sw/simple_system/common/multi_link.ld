ENTRY(_start)

SECTIONS
{
    /* First ELF at 0x1000000 */
    . = 0x1000000;
    .text.elf1 : { elf1.o(.text) }
    .data.elf1 : { elf1.o(.data) }

    /* Second ELF at 0x1400000 */
    . = 0x1400000;
    .text.elf2 : { elf2.o(.text) }
    .data.elf2 : { elf2.o(.data) }

    /* Third ELF at 0x1800000 */
    . = 0x1800000;
    .text.elf3 : { elf3.o(.text) }
    .data.elf3 : { elf3.o(.data) }

    /* Fourth ELF at 0x1C00000 */
    . = 0x1C00000;
    .text.elf4 : { elf4.o(.text) }
    .data.elf4 : { elf4.o(.data) }

    /* Common sections */
    .bss : { *(.bss) }
    . = ALIGN(4K);
    .stack : { *(.stack) }
}
