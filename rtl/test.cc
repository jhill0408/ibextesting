// Copyright lowRISC contributors.Add commentMore actions
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ibex_multicore_system.h"

int main(int argc, char **argv) {
  MulticoreSystem multicore_system(
      "TOP.ibex_multicore_system.u_ram1.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.u_ram2.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.u_ram3.u_ram.gen_generic.u_impl_generic", 1024*1024/4,
      "TOP.ibex_multicore_system.u_ram4.u_ram.gen_generic.u_impl_generic", 1024*1024/4
  );

  return multicore_system.Main(argc, argv);
}
