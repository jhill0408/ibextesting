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

int main(int argc, char **argv) {
  pcount_enable(0);
  pcount_reset();
  pcount_enable(1);
  pcount_enable(0);
  timer_enable(2000);
  uint64_t last_elapsed_time = get_elapsed_time();
  int test4;
  asm volatile ("csrr %0, mhartid" : "=r"(test4));

    if (test4 == 0) {
        int firstrow = M/4 * test4;
        int lastrow = (M/4 * (test4+1));
        int m;
        int b[M/4] = {0};
        int n;
        for (m=firstrow; m<lastrow; m++) {
            int edges = A_indptr[m+1] - A_indptr[m];
            for(n=0; n < edges; n++){
                b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];
            }
            
        }

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
            :
            : "r"(b[0])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
            :
            : "r"(b[1])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
            :
            : "r"(b[2])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
            :
            : "r"(b[3])
        ); // no clobber cuz modifying mprf
     
    } else if (test4 == 1) {

        int firstrow = M/4 * test4;
        int lastrow = (M/4 * (test4+1));
        int m;
        int b[M/4] = {0};
        int n;
        for (m=firstrow; m<lastrow; m++) {
            int edges = A_indptr[m+1] - A_indptr[m];
            for(n=0; n < edges; n++){
                b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];
            }
        }

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
            :
            : "r"(b[0])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
            :
            : "r"(b[1])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
            :
            : "r"(b[2])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
            :
            : "r"(b[3])
        ); // no clobber cuz modifying mprf

    } else if (test4 == 2) {

        int firstrow = M/4 * test4;
        int lastrow = (M/4 * (test4+1));
        int m;
        int b[M/4] = {0};
        int n;
        for (m=firstrow; m<lastrow; m++) {
            int edges = A_indptr[m+1] - A_indptr[m];
            for(n=0; n < edges; n++){
                b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];
            }
        }

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
            :
            : "r"(b[0])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
            :
            : "r"(b[1])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
            :
            : "r"(b[2])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
            :
            : "r"(b[3])
        ); // no clobber cuz modifying mprf
     

    } else if (test4 == 3) {

        int firstrow = M/4 * test4;
        int lastrow = (M/4 * (test4+1));
        int m;
        int b[M/4] = {0};
        int n;
        for (m=firstrow; m<lastrow; m++) {
            int edges = A_indptr[m+1] - A_indptr[m];
            for(n=0; n < edges; n++){
                b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];
            }
        }

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
            :
            : "r"(b[0])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
            :
            : "r"(b[1])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
            :
            : "r"(b[2])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
            :
            : "r"(b[3])
        ); // no clobber cuz modifying mprf

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
