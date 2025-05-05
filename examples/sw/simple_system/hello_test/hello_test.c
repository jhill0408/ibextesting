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
#define NUMCORES 10

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

    #define MOVE_MPRF_TO_GPRF(dest_var, src_reg)                   \
    asm volatile (                                             \
        ".insn r 0x0B, 0b001, 0x00, %0, " #src_reg ", x0"       \
        : "=r"(dest_var)                                        \
        :                                                      \
        :                                                      \
    );






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

  int firstrow = M/NUMCORES * test4;
  int lastrow = (M/NUMCORES * (test4+1));
  int m;
  int b[M/NUMCORES] = {0};
  int n;
  for (m=firstrow; m<lastrow; m++) {
    int edges = A_indptr[m+1] - A_indptr[m];
    for(n=0; n < edges; n++){
        b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];       
    }

    int baddr = NUMCORES-1;
        baddr = (baddr << 5);
        baddr = baddr + m + 1;
        if (test4 != NUMCORES - 1) {
            switch (m-firstrow+1) {
                case 1: MOVE_GPRF_TO_MPRF(x1, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x16, baddr); SEND_MPRF(x1, x16); break;
                case 2: MOVE_GPRF_TO_MPRF(x2, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x17, baddr); SEND_MPRF(x2, x17); break;
                case 3: MOVE_GPRF_TO_MPRF(x3, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x18, baddr); SEND_MPRF(x3, x18); break;
                case 4: MOVE_GPRF_TO_MPRF(x4, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x19, baddr); SEND_MPRF(x4, x19); break;
                case 5: MOVE_GPRF_TO_MPRF(x5, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x20, baddr); SEND_MPRF(x5, x20); break;
                case 6: MOVE_GPRF_TO_MPRF(x6, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x21, baddr); SEND_MPRF(x6, x21); break;
                case 7: MOVE_GPRF_TO_MPRF(x7, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x22, baddr); SEND_MPRF(x7, x22); break;
                case 8: MOVE_GPRF_TO_MPRF(x8, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x23, baddr); SEND_MPRF(x8, x23); break;
                case 9: MOVE_GPRF_TO_MPRF(x9, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x24, baddr); SEND_MPRF(x9, x24); break;
                case 10: MOVE_GPRF_TO_MPRF(x10, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x25, baddr); SEND_MPRF(x10, x25); break;
                case 11: MOVE_GPRF_TO_MPRF(x11, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x26, baddr); SEND_MPRF(x11, x26); break;
                case 12: MOVE_GPRF_TO_MPRF(x12, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x27, baddr); SEND_MPRF(x12, x27); break;
                case 13: MOVE_GPRF_TO_MPRF(x13, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x28, baddr); SEND_MPRF(x13, x28); break;
                case 14: MOVE_GPRF_TO_MPRF(x14, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x29, baddr); SEND_MPRF(x14, x29); break;
                case 15: MOVE_GPRF_TO_MPRF(x15, b[m-firstrow]); MOVE_GPRF_TO_MPRF(x30, baddr); SEND_MPRF(x15, x30); break;
            }
        } else {
          char testt[32];
          //   snprintf(testt, sizeof(testt), "%d", (m-firstrow+1));
          //   puts(testt);
          //   putchar('\n');
          //   snprintf(testt, sizeof(testt), "%d", b[m-firstrow]);
          //   puts(testt);
          //   putchar('\n');
            switch (m-firstrow+1) {
                case 1: MOVE_GPRF_TO_MPRF(x31, b[m-firstrow]); break;
                case 2: MOVE_GPRF_TO_MPRF(x30, b[m-firstrow]); break;
                case 3: MOVE_GPRF_TO_MPRF(x29, b[m-firstrow]); break;
                case 4: MOVE_GPRF_TO_MPRF(x28, b[m-firstrow]); break;
                case 5: MOVE_GPRF_TO_MPRF(x27, b[m-firstrow]); break;
                case 6: MOVE_GPRF_TO_MPRF(x26, b[m-firstrow]); break;
                case 7: MOVE_GPRF_TO_MPRF(x25, b[m-firstrow]); break;
                case 8: MOVE_GPRF_TO_MPRF(x24, b[m-firstrow]); break;
                case 9: MOVE_GPRF_TO_MPRF(x23, b[m-firstrow]); break;
                case 10: MOVE_GPRF_TO_MPRF(x22, b[m-firstrow]); break;
                case 11: MOVE_GPRF_TO_MPRF(x21, b[m-firstrow]); break;
                case 12: MOVE_GPRF_TO_MPRF(x20, b[m-firstrow]); break;
                case 13: MOVE_GPRF_TO_MPRF(x19, b[m-firstrow]); break;
                case 14: MOVE_GPRF_TO_MPRF(x18, b[m-firstrow]); break;
                case 15: MOVE_GPRF_TO_MPRF(x17, b[m-firstrow]); break;
            }

        }
            
  }

  if (test4 == NUMCORES - 1) {
    int done = 0;
    int done1 = 0;
    int done2 = 0;
    int done3 = 0;

    while (done == 0 && done1 == 0 && done2 == 0 && done3 == 0) { // maybe better for sum of the 4 to be > 1
        switch (M) {
            case 4: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 5: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4);  break;
            case 6: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4);  break;
            case 7: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4);  break;
            case 8: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4);  break;
            case 9: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4);  break;
            case 10: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 11: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 12: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 13: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 14: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 15: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 16: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 17: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 18: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 19: MOVE_MPRF_TO_GPRF(done, x1); MOVE_MPRF_TO_GPRF(done1, x2); MOVE_MPRF_TO_GPRF(done2, x3); MOVE_MPRF_TO_GPRF(done3, x4); break;
            case 20: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 21: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 22: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 23: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 24: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 25: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 26: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 27: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 28: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 29: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 30: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;
            case 31: MOVE_MPRF_TO_GPRF(done, x15); MOVE_MPRF_TO_GPRF(done1, x14); MOVE_MPRF_TO_GPRF(done2, x13); MOVE_MPRF_TO_GPRF(done3, x12); break;

        }

    }
    int outt[32] = {0};
    int i = 0;
    for ( i = 0; i < (M/NUMCORES * (NUMCORES - 1)); i++) {
        switch (i+1) {
            case 1: MOVE_MPRF_TO_GPRF(outt[i], x1); break;
            case 2: MOVE_MPRF_TO_GPRF(outt[i], x2); break;
            case 3: MOVE_MPRF_TO_GPRF(outt[i], x3); break;
            case 4: MOVE_MPRF_TO_GPRF(outt[i], x4); break;
            case 5: MOVE_MPRF_TO_GPRF(outt[i], x5); break;
            case 6: MOVE_MPRF_TO_GPRF(outt[i], x6); break;
            case 7: MOVE_MPRF_TO_GPRF(outt[i], x7); break;
            case 8: MOVE_MPRF_TO_GPRF(outt[i], x8); break;
            case 9: MOVE_MPRF_TO_GPRF(outt[i], x9); break;
            case 10: MOVE_MPRF_TO_GPRF(outt[i], x10); break;
            case 11: MOVE_MPRF_TO_GPRF(outt[i], x11); break;
            case 12: MOVE_MPRF_TO_GPRF(outt[i], x12); break;
            case 13: MOVE_MPRF_TO_GPRF(outt[i], x13); break;
            case 14: MOVE_MPRF_TO_GPRF(outt[i], x14); break;
            case 15: MOVE_MPRF_TO_GPRF(outt[i], x15); break;
            case 16: MOVE_MPRF_TO_GPRF(outt[i], x16); break;
            case 17: MOVE_MPRF_TO_GPRF(outt[i], x17); break;
            case 18: MOVE_MPRF_TO_GPRF(outt[i], x18); break;
            case 19: MOVE_MPRF_TO_GPRF(outt[i], x19); break;
            case 20: MOVE_MPRF_TO_GPRF(outt[i], x20); break;
            case 21: MOVE_MPRF_TO_GPRF(outt[i], x21); break;
            case 22: MOVE_MPRF_TO_GPRF(outt[i], x22); break;
            case 23: MOVE_MPRF_TO_GPRF(outt[i], x23); break;
            case 24: MOVE_MPRF_TO_GPRF(outt[i], x24); break;
            case 25: MOVE_MPRF_TO_GPRF(outt[i], x25); break;
            case 26: MOVE_MPRF_TO_GPRF(outt[i], x26); break;
            case 27: MOVE_MPRF_TO_GPRF(outt[i], x27); break;
            case 28: MOVE_MPRF_TO_GPRF(outt[i], x28); break;
            case 29: MOVE_MPRF_TO_GPRF(outt[i], x29); break;
            case 30: MOVE_MPRF_TO_GPRF(outt[i], x30); break;
            case 31: MOVE_MPRF_TO_GPRF(outt[i], x31); break;
        }

    }

    for (i = (M/NUMCORES * (NUMCORES - 1)); i < M; i++) {
        switch (i+1 - (M/NUMCORES * (NUMCORES-1))) {
            case 1: MOVE_MPRF_TO_GPRF(outt[i], x31); break;
            case 2: MOVE_MPRF_TO_GPRF(outt[i], x30); break;
            case 3: MOVE_MPRF_TO_GPRF(outt[i], x29); break;
            case 4: MOVE_MPRF_TO_GPRF(outt[i], x28); break;
            case 5: MOVE_MPRF_TO_GPRF(outt[i], x27); break;
            case 6: MOVE_MPRF_TO_GPRF(outt[i], x26); break;
            case 7: MOVE_MPRF_TO_GPRF(outt[i], x25); break;
            case 8: MOVE_MPRF_TO_GPRF(outt[i], x24); break;
            case 9: MOVE_MPRF_TO_GPRF(outt[i], x23); break;
            case 10: MOVE_MPRF_TO_GPRF(outt[i], x22); break;
            case 11: MOVE_MPRF_TO_GPRF(outt[i], x21); break;
            case 12: MOVE_MPRF_TO_GPRF(outt[i], x20); break;
        }

    }

    for (i = 0; i < M; i++) {
        char testchar[32];
        snprintf(testchar, sizeof(testchar), "%d", outt[i]);
        puts(testchar);
        putchar('\n');

    }

  }

    int count = 4;

    while (count < 500) {
      count = count + 1;
      asm volatile("wfi");

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
