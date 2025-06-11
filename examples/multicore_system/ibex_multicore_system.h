// Copyright lowRISC contributors.Add commentMore actions
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"

class MulticoreSystem {
 public:
  MulticoreSystem(const char *ram1_hier_path, int ram1_size_words, const char *ram2_hier_path, int ram2_size_words, const char *ram3_hier_path, int ram3_size_words, const char *ram4_hier_path, int ram4_size_words);
  virtual ~MulticoreSystem() {}
  virtual int Main(int argc, char **argv);

  // Return an ISA string, as understood by Spike, for the system being
  // simulated.
  std::string GetIsaString() const;

 protected:
  ibex_multicore_system _top;
  VerilatorMemUtil _memutil;
  MemArea _ram1;
  MemArea _ram2;
  MemArea _ram3;
  MemArea _ram4;

  virtual int Setup(int argc, char **argv, bool &exit_app);
  virtual void Run();
  //virtual void RunCores();
  virtual bool Finish();
};
