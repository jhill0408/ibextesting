// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include "dataset.h"
#include <stdio.h>

#define CORE0_BASE 0x100000
#define CORE1_BASE 0x140000
#define CORE2_BASE 0x180000
#define CORE3_BASE 0x1C0000
#define NUMCORES 4

#define MOVE_GPRF_TO_MPRF(dest_reg, src_val)               \
    asm volatile (                                          \
        ".insn r 0x0B, 0x0, 0x00, " #dest_reg ", %0, x0"     \
        :                                                   \
        : "r"(src_val)                                      \
    );

    /*
    #define SEND_MPRF(dest_reg, addr_reg)                      \
    asm volatile (                                                  \
        ".insn r 0x2B, 0b001, 0x00, %0, " #dest_reg ", " #addr_reg   \
        : "=r"(test3)                                              \
        :                                                           \
    );
*/
    #define SEND_MPRF(dest_var, addr_var)                           \
    asm volatile (                                                       \
        ".insn r 0x2B, 0b001, 0x00, %0, %1, %2"                          \
        : "=r"(test3)                                                  \
        : "r"(dest_var), "r"(addr_var)                                   \
        :                                                                \
    )


    #define SEND_DESCRIPTOR_MPRF(dest_reg, addr_reg)                      \
    asm volatile (                                                  \
        ".insn r 0x2B, 0b011, 0x00, %0, " #dest_reg ", " #addr_reg   \
        : "=r"(test3)                                              \
        :                                                           \
    );

#define MOVE_MPRF_TO_GPRF(dest_var, src_var)                        \
    asm volatile (                                                  \
        ".insn r 0x0B, 0b001, 0x00, %0, %1, x0"                     \
        : "=r"(dest_var)                                            \
        : "r"(src_var)                                              \
        :                                                           \
    )


int row2core(int rownum)
{
    const int rows_per_core = M / NUMCORES;   // base load
    const int extra_rows    = M % NUMCORES;   // first ‘extra_rows’ cores get one more

    /* rows 0 … (rows_per_core+1)*extra_rows - 1 go to the fatter cores */
    if (rownum < (rows_per_core + 1) * extra_rows) {
        return rownum / (rows_per_core + 1);
    }

    /* remaining rows map evenly to the leaner cores */
    return (rownum - extra_rows) / rows_per_core;
}






int main(int argc, char **argv) {

  pcount_enable(0);
  pcount_reset();
  pcount_enable(1);
  pcount_enable(0);
  timer_enable(2000);
  uint64_t last_elapsed_time = get_elapsed_time();
  int test4;
  int test3;
  asm volatile ("csrr %0, mhartid" : "=r"(test4));


  if (test4 == 0) {
    /*
    int t1 = 1;
    int t2 = 2;
    int t3 = 3;
    int addr = 0b00000000000000000000000000100001;
    MOVE_GPRF_TO_MPRF(x1, t1);
    MOVE_GPRF_TO_MPRF(x2, t2);
    MOVE_GPRF_TO_MPRF(x3, t3);
    MOVE_GPRF_TO_MPRF(x4, addr);
    MOVE_GPRF_TO_MPRF(x5, addr+1);
    MOVE_GPRF_TO_MPRF(x6, addr+2);

    SEND_MPRF(x1, x4);
    SEND_MPRF(x2, x5);
    SEND_MPRF(x3, x6);
    */

    int t1 = 0b00000000000000010000000000000010; // initial addr
    int t2 = 1; // imm
    int t3 = 2; // imm
    test3 = 5;
    test4 = 6;
    int t4 = 0b00100000000000000000000000001010; // send value from mprf
    int t5 = 2; // length
    int t6done = 0;
    int t6;
    int t7;
    int t8 = 0b00100000000000000000000000000011; // value from mprf
    int t9 = 0; // end
    int x[3] = {5, 6, 7};

    int y = 31;              
    t6 = &x;
    t6 = t6 + 0b01000000000000000000000000000000; // value form mem
    t7 = &y;
    t7 = t7 + 0b01000000000000000000000000000000; // value from emm
    int t10;
    t10 = 0;
    int test1;
    test1 = 10;
    
    puthex(t10);
    putchar('\n');
    puthex(t8);
    
    MOVE_GPRF_TO_MPRF(x1, t1);
    MOVE_GPRF_TO_MPRF(x2, t2);
    MOVE_GPRF_TO_MPRF(x3, t3);
    MOVE_GPRF_TO_MPRF(x4, t6);
    MOVE_GPRF_TO_MPRF(x5, t5);
    MOVE_GPRF_TO_MPRF(x6, t6done);
   // MOVE_GPRF_TO_MPRF(x7, t7);
   // MOVE_GPRF_TO_MPRF(x8, t8);
   // MOVE_GPRF_TO_MPRF(x9, t9);
   // MOVE_GPRF_TO_MPRF(x10, test3);
    MOVE_GPRF_TO_MPRF(x11, test4);
    int dest;
    int addr;
    dest = 3;
    addr = 1;
    SEND_MPRF(dest, addr);
    SEND_MPRF(dest, addr);
    SEND_MPRF(dest, addr);
    //SEND_DESCRIPTOR_MPRF(x1, x1);
    dest = 11;
    SEND_MPRF(dest, addr);

    int elev;
    elev = 11;

    MOVE_MPRF_TO_GPRF(test1, elev);
    MOVE_GPRF_TO_MPRF(x11, test1);
    SEND_MPRF(dest, addr);



  }



  while (last_elapsed_time <= 4) {
    uint64_t cur_time = get_elapsed_time();
    if (cur_time != last_elapsed_time) {
      last_elapsed_time = cur_time;
    }
    asm volatile("wfi");
  }

  return 0;
}
