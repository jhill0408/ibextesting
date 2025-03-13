// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ibex_multicore_system.h"

int main(int argc, char **argv) {
  MulticoreSystem multicore_system(
      "TOP.ibex_multicore_system.u_ram.u_ram.gen_generic.u_impl_generic", //will need to change this likely, add 2 rams
      1024 * 1024); // may need to divide by 4 and multiply by 16 if increasing size

  return multicore_system.Main(argc, argv);
}
