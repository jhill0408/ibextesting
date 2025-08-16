// Copyright lowRISC contributors.Add commentMore actions
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilated_toplevel.h"
#include "verilator_memutil.h"

class MulticoreSystem {
 public:
  MulticoreSystem(const char *ram1_hier_path, int ram1_size_words, const char *ram2_hier_path, int ram2_size_words, const char *ram3_hier_path, int ram3_size_words, const char *ram4_hier_path, int ram4_size_words, const char *ram5_hier_path, int ram5_size_words, const char *ram6_hier_path, int ram6_size_words, const char *ram7_hier_path, int ram7_size_words, const char *ram8_hier_path, int ram8_size_words, const char *ram9_hier_path, int ram9_size_words, const char *ram10_hier_path, int ram10_size_words, const char *ram11_hier_path, int ram11_size_words, const char *ram12_hier_path, int ram12_size_words, const char *ram13_hier_path, int ram13_size_words, const char *ram14_hier_path, int ram14_size_words, const char *ram15_hier_path, int ram15_size_words, const char *ram16_hier_path, int ram16_size_words, const char *ram17_hier_path, int ram17_size_words, const char *ram18_hier_path, int ram18_size_words, const char *ram19_hier_path, int ram19_size_words, const char *ram20_hier_path, int ram20_size_words, const char *ram21_hier_path, int ram21_size_words, const char *ram22_hier_path, int ram22_size_words, const char *ram23_hier_path, int ram23_size_words, const char *ram24_hier_path, int ram24_size_words, const char *ram25_hier_path, int ram25_size_words, const char *ram26_hier_path, int ram26_size_words, const char *ram27_hier_path, int ram27_size_words, const char *ram28_hier_path, int ram28_size_words, const char *ram29_hier_path, int ram29_size_words, const char *ram30_hier_path, int ram30_size_words, const char *ram31_hier_path, int ram31_size_words, const char *ram32_hier_path, int ram32_size_words);
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
  MemArea _ram5;
  MemArea _ram6;
  MemArea _ram7;
  MemArea _ram8;
  MemArea _ram9;
  MemArea _ram10;
  MemArea _ram11;
  MemArea _ram12;
  MemArea _ram13;
  MemArea _ram14;
  MemArea _ram15;
  MemArea _ram16;
  MemArea _ram17;
  MemArea _ram18;
  MemArea _ram19;
  MemArea _ram20;
  MemArea _ram21;
  MemArea _ram22;
  MemArea _ram23;
  MemArea _ram24;
  MemArea _ram25;
  MemArea _ram26;
  MemArea _ram27;
  MemArea _ram28;
  MemArea _ram29;
  MemArea _ram30;
  MemArea _ram31;
  MemArea _ram32;

  virtual int Setup(int argc, char **argv, bool &exit_app);
  virtual void Run();
  //virtual void RunCores();
  virtual bool Finish();
};
