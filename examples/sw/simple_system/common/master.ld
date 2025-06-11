/* master.ld */
SECTIONS {
  .core0_text 0x100000 : { core0.o(.text) }
  .core0_data 0x110000 : { core0.o(.data) }

  .core1_text 0x140000 : { core1.o(.text) }
  .core1_data 0x150000 : { core1.o(.data) }

  .core2_text 0x180000 : { core2.o(.text) }
  .core2_data 0x190000 : { core2.o(.data) }

  .core3_text 0x1C0000 : { core3.o(.text) }
  .core3_data 0x1D0000 : { core3.o(.data) }


}