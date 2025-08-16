// Copyright lowRISC contributors.Add commentMore actions
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ibex_multicore_system.h"

int main(int argc, char **argv) {
  MulticoreSystem multicore_system(
      "TOP.ibex_multicore_system.gen_rams[0].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[1].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[2].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[3].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[4].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[5].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[6].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[7].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[8].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[9].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[10].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[11].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[12].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[13].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[14].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[15].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[16].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[17].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[18].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[19].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[20].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[21].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[22].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[23].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[24].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[25].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[26].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[27].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[28].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[29].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[30].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.gen_rams[31].u_ram.u_ram.gen_generic.u_impl_generic", 1024*1024/4
  );

  return multicore_system.Main(argc, argv);
}
