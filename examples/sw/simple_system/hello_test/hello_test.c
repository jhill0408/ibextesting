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
  int test3;
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

        int b0_addr= 0b0001100001; // next try having a base addr and adding 1 each time
        int b1_addr= 0b0001100010;
        int b2_addr= 0b0001100011;
        int b3_addr= 0b0001100100;

        asm volatile (
          ".insn r 0x0B, 0x0, 0x00, x5, %0, x0" // moving something in gprf to mprf[5]
          :
          : "r"(b0_addr)
      ); // no clobber cuz modifying mprf

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x6, %0, x0" // moving something in gprf to mprf[6]
        :
        : "r"(b1_addr)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x7, %0, x0" // moving something in gprf to mprf[7]
      :
      : "r"(b2_addr)
  ); // no clobber cuz modifying mprf

  asm volatile (
    ".insn r 0x0B, 0x0, 0x00, x8, %0, x0" // moving something in gprf to mprf[8]
    :
    : "r"(b3_addr)
); // no clobber cuz modifying mprf


        asm volatile ( // sending b[0] (from core1 MPRF[1]) to core 0 MPRF[5] (addr info in core1 MPRF[5])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x5"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[1] (from core1 MPRF[2]) to core 0 MPRF[6] (addr info in core1 MPRF[6])
 		".insn r 0x2B, 0b001, 0x00, %0, x2, x6"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[2] (from core1 MPRF[3]) to core 0 MPRF[7] (addr info in core1 MPRF[7])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x7"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[3] (from core1 MPRF[4]) to core 0 MPRF[8] (addr info in core1 MPRF[8])
 		".insn r 0x2B, 0b001, 0x00, %0, x4, x8"
  		:"=r"(test3)
		:
		 
  		);

    

       
     
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

        int b0_addr= 0b0001100101; // next try having a base addr and adding 1 each time
        int b1_addr= 0b0001100110;
        int b2_addr= 0b0001100111;
        int b3_addr= 0b0001101000;

        asm volatile (
          ".insn r 0x0B, 0x0, 0x00, x5, %0, x0" // moving something in gprf to mprf[5]
          :
          : "r"(b0_addr)
      ); // no clobber cuz modifying mprf

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x6, %0, x0" // moving something in gprf to mprf[6]
        :
        : "r"(b1_addr)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x7, %0, x0" // moving something in gprf to mprf[7]
      :
      : "r"(b2_addr)
  ); // no clobber cuz modifying mprf

  asm volatile (
    ".insn r 0x0B, 0x0, 0x00, x8, %0, x0" // moving something in gprf to mprf[8]
    :
    : "r"(b3_addr)
); // no clobber cuz modifying mprf


        asm volatile ( // sending b[0] (from core1 MPRF[1]) to core 0 MPRF[5] (addr info in core1 MPRF[5])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x5"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[1] (from core1 MPRF[2]) to core 0 MPRF[6] (addr info in core1 MPRF[6])
 		".insn r 0x2B, 0b001, 0x00, %0, x2, x6"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[2] (from core1 MPRF[3]) to core 0 MPRF[7] (addr info in core1 MPRF[7])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x7"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[3] (from core1 MPRF[4]) to core 0 MPRF[8] (addr info in core1 MPRF[8])
 		".insn r 0x2B, 0b001, 0x00, %0, x4, x8"
  		:"=r"(test3)
		:
		 
  		);

        

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

        int b0_addr= 0b0001101001; // next try having a base addr and adding 1 each time
        int b1_addr= 0b0001101010;
        int b2_addr= 0b0001101011;
        int b3_addr= 0b0001101100;

        asm volatile (
          ".insn r 0x0B, 0x0, 0x00, x5, %0, x0" // moving something in gprf to mprf[5]
          :
          : "r"(b0_addr)
      ); // no clobber cuz modifying mprf

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x6, %0, x0" // moving something in gprf to mprf[6]
        :
        : "r"(b1_addr)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x7, %0, x0" // moving something in gprf to mprf[7]
      :
      : "r"(b2_addr)
  ); // no clobber cuz modifying mprf

  asm volatile (
    ".insn r 0x0B, 0x0, 0x00, x8, %0, x0" // moving something in gprf to mprf[8]
    :
    : "r"(b3_addr)
); // no clobber cuz modifying mprf


        asm volatile ( // sending b[0] (from core1 MPRF[1]) to core 0 MPRF[5] (addr info in core1 MPRF[5])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x5"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[1] (from core1 MPRF[2]) to core 0 MPRF[6] (addr info in core1 MPRF[6])
 		".insn r 0x2B, 0b001, 0x00, %0, x2, x6"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[2] (from core1 MPRF[3]) to core 0 MPRF[7] (addr info in core1 MPRF[7])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x7"
  		:"=r"(test3)
		:
		 
  		);

      asm volatile ( // sending b[3] (from core1 MPRF[4]) to core 0 MPRF[8] (addr info in core1 MPRF[8])
 		".insn r 0x2B, 0b001, 0x00, %0, x4, x8"
  		:"=r"(test3)
		:
		 
  		);
     

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
            ".insn r 0x0B, 0x0, 0x00, x13, %0, x0" // moving something in gprf to mprf[1]
            :
            : "r"(b[0])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x14, %0, x0" // moving something in gprf to mprf[2]
            :
            : "r"(b[1])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x15, %0, x0" // moving something in gprf to mprf[3]
            :
            : "r"(b[2])
        ); // no clobber cuz modifying mprf

        asm volatile (
            ".insn r 0x0B, 0x0, 0x00, x16, %0, x0" // moving something in gprf to mprf[4]
            :
            : "r"(b[3])
        ); // no clobber cuz modifying mprf

      }

    //testing
    asm volatile ("csrr %0, mhartid" : "=r"(test4));

    if (test4 == 3) {
      int done = 0;
      
      while (done == 0) {
        asm volatile (
          ".insn r 0x0B, 0b001, 0x00, %0, x8, x0" // gprf is written the value of mprf[16]
          :"=r"(done)
          : 
          : // double check how to clobber, if its even necessary
      );
      }
      
      int outt[16] = {0};
      asm volatile (
        ".insn r 0x0B, 0b001, 0x00, %0, x1, x0" // writing to gprf
        :"=r"(outt[0])
        : 
        : // double check how to clobber, if its even necessary
    );
    asm volatile (
      ".insn r 0x0B, 0b001, 0x00, %0, x2, x0" // writing to gprf
      :"=r"(outt[1])
      : 
      : // double check how to clobber, if its even necessary
  );
  asm volatile (
    ".insn r 0x0B, 0b001, 0x00, %0, x3, x0" // writing to gprf
    :"=r"(outt[2])
    : 
    : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x4, x0" // writing to gprf
  :"=r"(outt[3])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x5, x0" // writing to gprf
  :"=r"(outt[4])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x6, x0" // writing to gprf
  :"=r"(outt[5])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x7, x0" // writing to gprf
  :"=r"(outt[6])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x8, x0" // writing to gprf
  :"=r"(outt[7])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x9, x0" // writing to gprf
  :"=r"(outt[8])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x10, x0" // writing to gprf
  :"=r"(outt[9])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x11, x0" // writing to gprf
  :"=r"(outt[10])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x12, x0" // writing to gprf
  :"=r"(outt[11])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x13, x0" // writing to gprf
  :"=r"(outt[12])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x14, x0" // writing to gprf
  :"=r"(outt[13])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x15, x0" // writing to gprf
  :"=r"(outt[14])
  : 
  : // double check how to clobber, if its even necessary
);
asm volatile (
  ".insn r 0x0B, 0b001, 0x00, %0, x16, x0" // writing to gprf
  :"=r"(outt[15])
  : 
  : // double check how to clobber, if its even necessary
);

char testchar[32];
   snprintf(testchar, sizeof(testchar), "%d", outt[0]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[1]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[2]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[3]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[4]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[5]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[6]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[7]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[8]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[9]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[10]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[11]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[12]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[13]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[14]);
    puts(testchar);
    putchar('\n');
    snprintf(testchar, sizeof(testchar), "%d", outt[15]);
    puts(testchar);
    putchar('\n');
    }

    int count = 4;

    while (count < 1000) {
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
