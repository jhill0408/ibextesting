// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include <stdio.h>

#define CORE0_BASE 0x100000
#define CORE1_BASE 0x140000
#define CORE2_BASE 0x180000
#define CORE3_BASE 0x1C0000

void print_sp() {
  unsigned int sp;
  asm volatile("mv %0, sp" : "=r"(sp));
  puthex(sp);  // Print sp as hex
}


void init() {
  uint32_t hartid;
  asm volatile ("csrr %0, mhartid" : "=r"(hartid)); // Read core ID

  // Set stack pointer based on core ID
  switch (hartid) {
    case 0:
    asm volatile(
      "li   t0, %0\n"  
      "mv   sp, t0\n"   
      :
      : "i"((CORE0_BASE + 0x3FED0) & ~0xF)  // & ~0xF ensures stack is 16-byte aligned (ABI?)
      : "t0"
    );
    break;
    case 1: 
    asm volatile(
      "li   t0, %0\n"  
      "mv   sp, t0\n"   
      :
      : "i"((CORE1_BASE + 0x3FED0) & ~0xF)  // & ~0xF ensures stack is 16-byte aligned (ABI?)
      : "t0"
    );
    break;
    case 2:
    asm volatile(
      "li   t0, %0\n"  
      "mv   sp, t0\n"   
      :
      : "i"((CORE2_BASE + 0x3FED0) & ~0xF)  // & ~0xF ensures stack is 16-byte aligned (ABI?)
      : "t0"
    );
    break;
    case 3: 
    asm volatile(
      "li   t0, %0\n"  
      "mv   sp, t0\n"   
      :
      : "i"((CORE3_BASE + 0x3FED0) & ~0xF)  // & ~0xF ensures stack is 16-byte aligned (ABI?)
      : "t0"
    );
    break;
  }
  //main();
}

int main(int argc, char **argv) {

  pcount_enable(0);
  pcount_reset();
  pcount_enable(1);
  pcount_enable(0);
  timer_enable(2000);
  uint64_t last_elapsed_time = get_elapsed_time();
  int test4;
  asm volatile ("csrr %0, mhartid" : "=r"(test4));
/*
    if (test4 == 0) {
      puts("zeroth \n");
  } else if (test4 == 1) {
      puts("first \n");
  } else if (test4 == 2) {
      puts("second \n");
  } else if (test4 == 3) {
      puts("third \n");
  } else {
      puts("unknown \n");
  }
      */
    if (test4 == 1) {
      /*
      test1 = 0xAABB;
      test2 = 0b0000000000;
    asm volatile (
 		".insn r 0x2B, 0x0, 0x00, %0, %1, %2"
  		:"=r"(test3)
		:"r"(test1), "r"(test2)
  		);

      test1 = 0xCABB;
      test2 = 0b0000000001;
    asm volatile (
 		".insn r 0x2B, 0x0, 0x00, %0, %1, %2"
  		:"=r"(test3)
		:"r"(test1), "r"(test2)
  		);
      */
    }

    asm volatile ("csrr %0, mhartid" : "=r"(test4));

    if (test4 == 0) {
      int test3;
      test3 =0;
      int counter;
      int counter_addr;
      int token_addr;
      int token;
      counter = 1;
      counter_addr= 0b0000100001;
      token_addr = 0b0000100011;
      token = 1;
      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
        :
        : "r"(counter)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
      :
      : "r"(counter_addr)
  ); // no clobber cuz modifying mprf

  asm volatile (
    ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
    :
    : "r"(token)
); // no clobber cuz modifying mprf

asm volatile (
  ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
  :
  : "r"(token_addr)
); // no clobber cuz modifying mprf

asm volatile ( // sending 0x1 (from core0 MPRF[1]) to core 1 MPRF[1] (addr info in core0 MPRF[2])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x2"
  		:"=r"(test3)
		:
		 
  		);


      asm volatile ( // sending 0x1 (from core0 MPRF[3]) to core 1 MPRF[3] (addr info in core0 MPRF[4])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x4"
  		:"=r"(test3)
		:
		 
  		);

      token = 0;
      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
        :
        : "r"(token)
    ); // no clobber cuz modifying mprf


    } else if (test4 == 1) {
      int test3;
      test3 =0;
      int counter;
      int counter_addr;
      int token_addr;
      int token;
      counter_addr= 0b0001000001;
      token_addr = 0b0001000011;
      token = 0;

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
        :
        : "r"(counter_addr)
    ); // no clobber cuz modifying mprf
    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
      :
      : "r"(token_addr)
    ); // no clobber cuz modifying mprf

      while (token == 0) {
        asm volatile (
          ".insn r 0x0B, 0b001, 0x00, %0, x3, x0" // gprf[5] is written the value of mprf[1]
          :"=r"(token)
          : 
          : // double check how to clobber, if its even necessary
      );

      asm volatile (
        ".insn r 0x0B, 0b001, 0x00, %0, x1, x0" // gprf[5] is written the value of mprf[1]
        :"=r"(counter)
        : 
        : // double check how to clobber, if its even necessary
    );

      }

      counter = counter + 1;

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
        :
        : "r"(counter)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
      :
      : "r"(token)
  ); // no clobber cuz modifying mprf

      asm volatile ( // sending 0x1 (from core1 MPRF[1]) to core 2 MPRF[1] (addr info in core1 MPRF[2])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x2"
  		:"=r"(test3)
		:
		 
  		);


      asm volatile ( // sending 0x1 (from core1 MPRF[3]) to core 2 MPRF[3] (addr info in core1 MPRF[4])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x4"
  		:"=r"(test3)
		:
		 
  		);

      token = 0;
      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
        :
        : "r"(token)
    ); // no clobber cuz modifying mprf


    } else if (test4 == 2) {
      int test3;
      test3 =0;
      int counter;
      int counter_addr;
      int token_addr;
      int token;
      counter_addr= 0b0001100001;
      token_addr = 0b0001100011;
      token = 0;

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
        :
        : "r"(counter_addr)
    ); // no clobber cuz modifying mprf
    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x4, %0, x0" // moving something in gprf to mprf[4]
      :
      : "r"(token_addr)
    ); // no clobber cuz modifying mprf

      while (token == 0) {
        asm volatile (
          ".insn r 0x0B, 0b001, 0x00, %0, x3, x0" // gprf[5] is written the value of mprf[1]
          :"=r"(token)
          : 
          : // double check how to clobber, if its even necessary
      );

      asm volatile (
        ".insn r 0x0B, 0b001, 0x00, %0, x1, x0" // gprf[5] is written the value of mprf[1]
        :"=r"(counter)
        : 
        : // double check how to clobber, if its even necessary
    );

      }

      counter = counter + 1;

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
        :
        : "r"(counter)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
      :
      : "r"(token)
  ); // no clobber cuz modifying mprf

      asm volatile ( // sending 0x1 (from core2 MPRF[1]) to core 3 MPRF[1] (addr info in core2 MPRF[2])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x2"
  		:"=r"(test3)
		:
		 
  		);


      asm volatile ( // sending 0x1 (from core2 MPRF[3]) to core 3 MPRF[3] (addr info in core2 MPRF[4])
 		".insn r 0x2B, 0b001, 0x00, %0, x3, x4"
  		:"=r"(test3)
		:
		 
  		);

      token = 0;
      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x3, %0, x0" // moving something in gprf to mprf[3]
        :
        : "r"(token)
    ); // no clobber cuz modifying mprf

    } else if (test4 == 3) {

      //int test3;
      //test3 =0;
      int counter;
      //int counter_addr;
      //int token_addr;
      int token;
      //counter_addr= 0b0001100001;
      //token_addr = 0b0001100011;
      token = 0;

      while (token == 0) {
        asm volatile (
          ".insn r 0x0B, 0b001, 0x00, %0, x3, x0" // gprf[5] is written the value of mprf[1]
          :"=r"(token)
          : 
          : // double check how to clobber, if its even necessary
      );

      asm volatile (
        ".insn r 0x0B, 0b001, 0x00, %0, x1, x0" // gprf[5] is written the value of mprf[1]
        :"=r"(counter)
        : 
        : // double check how to clobber, if its even necessary
    );

      }

      counter = counter + 1;
      char testchar[6];
   snprintf(testchar, sizeof(testchar), "%d", counter);
    puts("output is:\n");
    //puts("lasflsflsalfsalfsalfsalfsalflsalfsalfsalfsalflsaflsafsaflsaflsalfa");
    puts(testchar);
    putchar('\n');

    }
/*
    if (test4 == 2) {
      test1 = 0xAABB;
      test2 = 0b0000100001;

      

    asm volatile (
      ".insn r 0x0B, 0b001, 0x00, x5, x1, x0" // gprf[5] is written the value of mprf[1]
      :
      : 
      : "x5" // clobbering cuz changing gprf
  );
    
    asm volatile ( // sending 0xAABB (from MPRF[1]) to core 1 MPRF[1] (addr info in MPRF[2])
 		".insn r 0x2B, 0b001, 0x00, %0, x1, x2"
  		:"=r"(test3)
		:
		 
  		);

      test1 = 0xEABB;
      test2 = 0b0000100010;
    asm volatile (
 		".insn r 0x2B, 0x0, 0x00, %0, %1, %2"
  		:"=r"(test3)
		:"r"(test1), "r"(test2)
		 
  		);
      
    }
      */
  
  

  while (last_elapsed_time <= 4) {
    uint64_t cur_time = get_elapsed_time();
    if (cur_time != last_elapsed_time) {
      last_elapsed_time = cur_time;

      if (last_elapsed_time & 1) {
	//   puts("Tick!\n");
      } else {
	// puts("Tock!\n");
      }
    }
    asm volatile("wfi");
  }

  return 0;
}
