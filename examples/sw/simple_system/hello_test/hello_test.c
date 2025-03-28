// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include <stdio.h>

int main(int argc, char **argv) {
  pcount_enable(0);
  pcount_reset();
  pcount_enable(1);

  puts("Hello simple system\n");
  // puthex(0xDEADBEEF);
  // putchar('\n');
  // puthex(0xBAADF00D);
  // putchar('\n');

  pcount_enable(0);

  // Enable periodic timer interrupt
  // (the actual timebase is a bit meaningless in simulation)
  timer_enable(2000);

  uint64_t last_elapsed_time = get_elapsed_time();
  int test1 = 9;
  int test2 = 2;
  int test3;

  asm volatile (
 		".insn r 0x0B, 0x0, 0x00, %0, %1, %2"
  		:"=r"(test3)
		:"r"(test1), "r"(test2)
		 
  		);
  char testchar[20];
  snprintf(testchar, sizeof(testchar), "%d", test3);
  puts("output is:\n");
  puts(testchar);
  putchar('\n');
  
  

  while (last_elapsed_time <= 4) {
    uint64_t cur_time = get_elapsed_time();
    if (cur_time != last_elapsed_time) {
      last_elapsed_time = cur_time;

      if (last_elapsed_time & 1) {
        puts("Tick!\n");
      } else {
        puts("Tock!\n");
      }
    }
    asm volatile("wfi");
  }

  return 0;
}
