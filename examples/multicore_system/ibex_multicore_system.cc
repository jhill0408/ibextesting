// Copyright lowRISC contributors. Add commentMore actions
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cassert>
#include <fstream>
#include <iostream>

#include "Vibex_multicore_system__Syms.h"
#include "ibex_pcounts.h"
#include "ibex_multicore_system.h"
#include "verilated_toplevel.h"
#include "verilator_memutil.h"
#include "verilator_sim_ctrl.h"

MulticoreSystem::MulticoreSystem(const char *ram1_hier_path, int ram1_size_words, const char *ram2_hier_path, int ram2_size_words, const char *ram3_hier_path, int ram3_size_words, const char *ram4_hier_path, int ram4_size_words )
    : _ram1(ram1_hier_path, ram1_size_words, 4),
      _ram2(ram2_hier_path, ram2_size_words, 4),
      _ram3(ram3_hier_path, ram3_size_words, 4),
      _ram4(ram4_hier_path, ram4_size_words, 4) {}

int MulticoreSystem::Main(int argc, char **argv) {
  bool exit_app;
  int ret_code = Setup(argc, argv, exit_app);

  if (exit_app) {
    return ret_code;
  }

  Run();
  //RunCores();

  if (!Finish()) {
    return 1;
  }

  return 0;
}

std::string MulticoreSystem::GetIsaString() const {
  const Vibex_multicore_system &top = _top;
  assert(top.ibex_multicore_system);

  std::string base = top.ibex_multicore_system->RV32E ? "rv32e" : "rv32i";

  std::string extensions;
  if (top.ibex_multicore_system->RV32M)
    extensions += "m";

  extensions += "c";

  switch (top.ibex_multicore_system->RV32B) {
    case 0:  // RV32BNone
      break;

    case 1:  // RV32BBalanced
      extensions += "_Zba_Zbb_Zbs_XZbf_XZbt";
      break;

    case 2:  // RV32BOTEarlGrey
      extensions += "_Zba_Zbb_Zbc_Zbs_XZbf_XZbp_XZbr_XZbt";
      break;

    case 3:  // RV32BFull
      extensions += "_Zba_Zbb_Zbc_Zbs_XZbe_XZbf_XZbp_XZbr_XZbt";
      break;
  }

  return base + extensions;
}

int MulticoreSystem::Setup(int argc, char **argv, bool &exit_app) {
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  simctrl.SetTop(&_top, &_top.IO_CLK, &_top.IO_RST_N,
                 VerilatorSimCtrlFlags::ResetPolarityNegative);

  std::cout << "RAM1" << std::endl;
  _memutil.RegisterMemoryArea("ram1", 0x00100000, &_ram1);
  std::cout << _ram1.GetSizeBytes() << std::endl;
  std::cout << "RAM2" << std::endl;
  _memutil.RegisterMemoryArea("ram2", 0x00200000, &_ram2);
  std::cout << _ram2.GetSizeBytes() << std::endl;
  std::cout << "RAM3" << std::endl;
  _memutil.RegisterMemoryArea("ram3", 0x00300000, &_ram3);
  std::cout << _ram3.GetSizeBytes() << std::endl;
  std::cout << "RAM4" << std::endl;
  _memutil.RegisterMemoryArea("ram4", 0x00400000, &_ram4);
  std::cout << _ram4.GetSizeBytes() << std::endl;
  simctrl.RegisterExtension(&_memutil);

  exit_app = false;
  return simctrl.ParseCommandArgs(argc, argv, exit_app);
}

void MulticoreSystem::Run() {
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  std::cout << "Simulation of Ibex" << std::endl
            << "==================" << std::endl
            << std::endl;

  simctrl.RunSimulation();
}

bool MulticoreSystem::Finish() {
  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();

  if (!simctrl.WasSimulationSuccessful()) {
    return false;
  }

  // Set the scope to the root scope, the ibex_pcount_string function otherwise
  // doesn't know the scope itself. Could be moved to ibex_pcount_string, but
  // would require a way to set the scope name from here, similar to MemUtil.
  svSetScope(svGetScopeFromName("TOP.ibex_multicore_system"));

  std::cout << "\nPerformance Counters" << std::endl
            << "====================" << std::endl;
  std::cout << ibex_pcount_string(false);

  std::ofstream pcount_csv("ibex_multicore_system_pcount.csv");
  pcount_csv << ibex_pcount_string(true);

  return true;
}