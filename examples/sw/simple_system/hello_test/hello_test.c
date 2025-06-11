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

    #define SEND_MPRF(dest_reg, addr_reg)                      \
    asm volatile (                                                  \
        ".insn r 0x2B, 0b001, 0x00, %0, " #dest_reg ", " #addr_reg   \
        : "=r"(test3)                                              \
        :                                                           \
    );

    #define SEND_DESCRIPTOR_MPRF(dest_reg, addr_reg)                      \
    asm volatile (                                                  \
        ".insn r 0x2B, 0b011, 0x00, %0, " #dest_reg ", " #addr_reg   \
        : "=r"(test3)                                              \
        :                                                           \
    );

    #define MOVE_MPRF_TO_GPRF(dest_var, src_reg)                   \
    asm volatile (                                             \
        ".insn r 0x0B, 0b001, 0x00, %0, " #src_reg ", x0"       \
        : "=r"(dest_var)                                        \
        :                                                      \
        :                                                      \
    );

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
    int t1 = 1;
    int t2 = 2;
    int t3 = 3;
    int addr = 0b00011000000000000000000000100001;
    MOVE_GPRF_TO_MPRF(x1, t1);
    MOVE_GPRF_TO_MPRF(x2, t2);
    MOVE_GPRF_TO_MPRF(x3, t3);
    MOVE_GPRF_TO_MPRF(x4, addr);

    SEND_DESCRIPTOR_MPRF(x1, x4);
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
