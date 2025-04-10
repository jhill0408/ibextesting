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
 // init();
  pcount_enable(0);
  pcount_reset();
  pcount_enable(1);
  //print_sp();

   // puts("Hello simple system\n");
  // puthex(0xDEADBEEF);
  // putchar('\n');
  // puthex(0xBAADF00D);
  // putchar('\n');

  pcount_enable(0);

  // Enable periodic timer interrupt
  // (the actual timebase is a bit meaningless in simulation)
  timer_enable(2000);

  uint64_t last_elapsed_time = get_elapsed_time();
  //int test1 = 9;
  //int test2 = 18;
  //int test3;

  //asm volatile (
 	//	".insn r 0x2B, 0x0, 0x00, %0, %1, %2"
  //		:"=r"(test3)
	//	:"r"(test1), "r"(test2)
		 
  //		);

  int test4;
 // int test = 10;
 // asm volatile (
 //   "mv s2, %0"
 //   :
 //   : "r"(test)
//);
asm volatile ("mv %0, x18" : "=r"(test4)); 

int test5;
asm volatile ("csrr %0, mhartid" : "=r"(test5));

test4 = 11;
test5 = test5 + test4;

    char testchar[6];
   snprintf(testchar, sizeof(testchar), "%d", test5);
    puts("output is:\n");
    //puts("lasflsflsalfsalfsalfsalfsalflsalfsalfsalfsalflsaflsafsaflsaflsalfa");
    puts(testchar);
    putchar('\n');

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
  
   snprintf(testchar, sizeof(testchar), "%d", test4);
    puts("core is:\n");
    //puts("lasflsflsalfsalfsalfsalfsalflsalfsalfsalfsalflsaflsafsaflsaflsalfa");
    puts(testchar);
    putchar('\n');

    int test1;
    int test2;
    int test3;
    test3 = 1;

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

    if (test4 == 2) {
      test1 = 0xAABB;
      test2 = 0b0000100001;

      asm volatile (
        ".insn r 0x0B, 0x0, 0x00, x1, %0, x0" // moving something in gprf to mprf[1]
        :
        : "r"(test1)
    ); // no clobber cuz modifying mprf

    asm volatile (
      ".insn r 0x0B, 0x0, 0x00, x2, %0, x0" // moving something in gprf to mprf[2]
      :
      : "r"(test2)
  ); // no clobber cuz modifying mprf

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
