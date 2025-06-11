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

  int firstrow = M/NUMCORES * test4;
  int lastrow = (M/NUMCORES * (test4+1));
  int remainder = M - (M/NUMCORES) * NUMCORES;
  int m;
  int b[M/NUMCORES + 1] = {0};
  int n;
  int k;
  int b_full[M] = {0};

  int increment = 15/NUMCORES;

  for (k = firstrow; k < lastrow; k=k+increment){
    int limit = ( k+increment < lastrow) ? (k+increment) : lastrow;
  for (m=k; m<limit; m++) {
    int edges = A_indptr[m+1] - A_indptr[m];
    for(n=0; n < edges; n++){
        b[m-firstrow] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];       
    }


            switch ((m%15)+1) {
                case 1: MOVE_GPRF_TO_MPRF(x1, b[m-firstrow]); break;
                case 2: MOVE_GPRF_TO_MPRF(x2, b[m-firstrow]); break;
                case 3: MOVE_GPRF_TO_MPRF(x3, b[m-firstrow]); break;
                case 4: MOVE_GPRF_TO_MPRF(x4, b[m-firstrow]); break;
                case 5: MOVE_GPRF_TO_MPRF(x5, b[m-firstrow]); break;
                case 6: MOVE_GPRF_TO_MPRF(x6, b[m-firstrow]); break;
                case 7: MOVE_GPRF_TO_MPRF(x7, b[m-firstrow]); break;
                case 8: MOVE_GPRF_TO_MPRF(x8, b[m-firstrow]); break;
                case 9: MOVE_GPRF_TO_MPRF(x9, b[m-firstrow]); break;
                case 10: MOVE_GPRF_TO_MPRF(x10, b[m-firstrow]); break;
                case 11: MOVE_GPRF_TO_MPRF(x11, b[m-firstrow]); break;
                case 12: MOVE_GPRF_TO_MPRF(x12, b[m-firstrow]); break;
                case 13: MOVE_GPRF_TO_MPRF(x13, b[m-firstrow]); break;
                case 14: MOVE_GPRF_TO_MPRF(x14, b[m-firstrow]); break;
                case 15: MOVE_GPRF_TO_MPRF(x15, b[m-firstrow]); break;
            }

            edges = s_index[m+1] - s_index[m];

            for(n=0; n < edges; n++){
                   int core_dest = row2core(invcol_index[s_index[m]+n]);
                   if (core_dest != test4) {
                   core_dest = core_dest << 5;
                   core_dest = core_dest + (m%15) + 1; // technically need to do % stuff, e.g. b[16] shoul dbe sent to x1  
                   switch ((m%15)+1) {
                case 1: MOVE_GPRF_TO_MPRF(x16, core_dest); SEND_MPRF(x1, x16); break;
                case 2: MOVE_GPRF_TO_MPRF(x17, core_dest); SEND_MPRF(x2, x17); break;
                case 3: MOVE_GPRF_TO_MPRF(x18, core_dest); SEND_MPRF(x3, x18); break;
                case 4: MOVE_GPRF_TO_MPRF(x19, core_dest); SEND_MPRF(x4, x19); break;
                case 5: MOVE_GPRF_TO_MPRF(x20, core_dest); SEND_MPRF(x5, x20); break;
                case 6: MOVE_GPRF_TO_MPRF(x21, core_dest); SEND_MPRF(x6, x21); break;
                case 7: MOVE_GPRF_TO_MPRF(x22, core_dest); SEND_MPRF(x7, x22); break;
                case 8: MOVE_GPRF_TO_MPRF(x23, core_dest); SEND_MPRF(x8, x23); break;
                case 9: MOVE_GPRF_TO_MPRF(x24, core_dest); SEND_MPRF(x9, x24); break;
                case 10: MOVE_GPRF_TO_MPRF(x25, core_dest); SEND_MPRF(x10, x25); break;
                case 11: MOVE_GPRF_TO_MPRF(x26, core_dest); SEND_MPRF(x11, x26); break;
                case 12: MOVE_GPRF_TO_MPRF(x27, core_dest); SEND_MPRF(x12, x27); break;
                case 13: MOVE_GPRF_TO_MPRF(x28, core_dest); SEND_MPRF(x13, x28); break;
                case 14: MOVE_GPRF_TO_MPRF(x29, core_dest); SEND_MPRF(x14, x29); break;
                case 15: MOVE_GPRF_TO_MPRF(x30, core_dest); SEND_MPRF(x15, x30); break;
            }   
                   } 
                }

  }

  if (test4 == 0) {
    int token_dest = (1<<5) + 31;
    int token = 1;
    MOVE_GPRF_TO_MPRF(x30, token_dest);
    MOVE_GPRF_TO_MPRF(x31, token);
    SEND_MPRF(x31, x30);
    token = 0;
    MOVE_GPRF_TO_MPRF(x31, token);
    while (token == 0) {
        MOVE_MPRF_TO_GPRF(token, x31);
    }
    // collect everything!!!!!!!!!!!!! HERE!
    int ii;

  for (ii = k; ii < limit; ii++) {
     switch ((ii%15)+1) {
            case 1: MOVE_MPRF_TO_GPRF(b_full[ii], x1); break;
            case 2: MOVE_MPRF_TO_GPRF(b_full[ii], x2); break;
            case 3: MOVE_MPRF_TO_GPRF(b_full[ii], x3); break;
            case 4: MOVE_MPRF_TO_GPRF(b_full[ii], x4); break;
            case 5: MOVE_MPRF_TO_GPRF(b_full[ii], x5); break;
            case 6: MOVE_MPRF_TO_GPRF(b_full[ii], x6); break;
            case 7: MOVE_MPRF_TO_GPRF(b_full[ii], x7); break;
            case 8: MOVE_MPRF_TO_GPRF(b_full[ii], x8); break;
            case 9: MOVE_MPRF_TO_GPRF(b_full[ii], x9); break;
            case 10: MOVE_MPRF_TO_GPRF(b_full[ii], x10); break;
            case 11: MOVE_MPRF_TO_GPRF(b_full[ii], x11); break;
            case 12: MOVE_MPRF_TO_GPRF(b_full[ii], x12); break;
            case 13: MOVE_MPRF_TO_GPRF(b_full[ii], x13); break;
            case 14: MOVE_MPRF_TO_GPRF(b_full[ii], x14); break;
            case 15: MOVE_MPRF_TO_GPRF(b_full[ii], x15); break;
        }

  }
    MOVE_GPRF_TO_MPRF(x30, token_dest);
    SEND_MPRF(x31, x30);
    token = 0;
    MOVE_GPRF_TO_MPRF(x31, token);

  } else {
    int token = 0;
    int token_dest = (((test4+1)%NUMCORES) << 5) + 31;
    while (token == 0) {
        MOVE_MPRF_TO_GPRF(token, x31);
    }
    MOVE_GPRF_TO_MPRF(x30, token_dest);
    SEND_MPRF(x31, x30);
    token = 0;
    MOVE_GPRF_TO_MPRF(x31, token);
    while (token == 0) {
        MOVE_MPRF_TO_GPRF(token, x31);
    }
    // COLLECT EVERYTHING HERE!!!!!!!!
    int ii;

  for (ii = k; ii < limit; ii++) {
     switch ((ii%15)+1) {
            case 1: MOVE_MPRF_TO_GPRF(b_full[ii], x1); break;
            case 2: MOVE_MPRF_TO_GPRF(b_full[ii], x2); break;
            case 3: MOVE_MPRF_TO_GPRF(b_full[ii], x3); break;
            case 4: MOVE_MPRF_TO_GPRF(b_full[ii], x4); break;
            case 5: MOVE_MPRF_TO_GPRF(b_full[ii], x5); break;
            case 6: MOVE_MPRF_TO_GPRF(b_full[ii], x6); break;
            case 7: MOVE_MPRF_TO_GPRF(b_full[ii], x7); break;
            case 8: MOVE_MPRF_TO_GPRF(b_full[ii], x8); break;
            case 9: MOVE_MPRF_TO_GPRF(b_full[ii], x9); break;
            case 10: MOVE_MPRF_TO_GPRF(b_full[ii], x10); break;
            case 11: MOVE_MPRF_TO_GPRF(b_full[ii], x11); break;
            case 12: MOVE_MPRF_TO_GPRF(b_full[ii], x12); break;
            case 13: MOVE_MPRF_TO_GPRF(b_full[ii], x13); break;
            case 14: MOVE_MPRF_TO_GPRF(b_full[ii], x14); break;
            case 15: MOVE_MPRF_TO_GPRF(b_full[ii], x15); break;
        }

  }
    MOVE_GPRF_TO_MPRF(x30, token_dest);
    SEND_MPRF(x31, x30);
    token = 0;
    MOVE_GPRF_TO_MPRF(x31, token);
    

  }

  



}































  m = (M/NUMCORES) * NUMCORES + test4;
  if (m < M) {
  int baddr = NUMCORES-1;
  baddr = (baddr << 5);
  baddr = baddr + m + 1;
  int edges = A_indptr[m+1] - A_indptr[m];
    for(n=0; n < edges; n++){
        b[M/NUMCORES] += A_data[A_indptr[m] + n] * x[A_indices[A_indptr[m] + n]];       
    }
    

    MOVE_GPRF_TO_MPRF(x15, b[M/NUMCORES]); 

     edges = s_index[m+1] - s_index[m];
                for(n=0; n < edges; n++){
                   int core_dest = invcol_index[s_index[m]+n];
                   if (core_dest != test4) {
                   core_dest = core_dest << 5;
                   core_dest = core_dest + m + 1; // technically need to do % stuff, e.g. b[16] shoul dbe sent to x1  

                MOVE_GPRF_TO_MPRF(x30, core_dest); 
                SEND_MPRF(x15, x30);
                   } 
                }
  }

































  if (test4 == NUMCORES - 1) {
    int done = 0;
    int done1 = 0;
    int done2 = 0;
    int done3 = 0;
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

    for (i = (M/NUMCORES * (NUMCORES - 1)); i < M/NUMCORES * NUMCORES; i++) {
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

    for (i = (M/NUMCORES * (NUMCORES)); i < M; i++) {
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
