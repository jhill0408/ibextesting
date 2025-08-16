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

MulticoreSystem::MulticoreSystem(const char *ram1_hier_path, int ram1_size_words, const char *ram2_hier_path, int ram2_size_words, const char *ram3_hier_path, int ram3_size_words, const char *ram4_hier_path, int ram4_size_words, const char *ram5_hier_path, int ram5_size_words, const char *ram6_hier_path, int ram6_size_words, const char *ram7_hier_path, int ram7_size_words, const char *ram8_hier_path, int ram8_size_words, const char *ram9_hier_path, int ram9_size_words, const char *ram10_hier_path, int ram10_size_words, const char *ram11_hier_path, int ram11_size_words, const char *ram12_hier_path, int ram12_size_words, const char *ram13_hier_path, int ram13_size_words, const char *ram14_hier_path, int ram14_size_words, const char *ram15_hier_path, int ram15_size_words, const char *ram16_hier_path, int ram16_size_words, const char *ram17_hier_path, int ram17_size_words, const char *ram18_hier_path, int ram18_size_words, const char *ram19_hier_path, int ram19_size_words, const char *ram20_hier_path, int ram20_size_words, const char *ram21_hier_path, int ram21_size_words, const char *ram22_hier_path, int ram22_size_words, const char *ram23_hier_path, int ram23_size_words, const char *ram24_hier_path, int ram24_size_words, const char *ram25_hier_path, int ram25_size_words, const char *ram26_hier_path, int ram26_size_words, const char *ram27_hier_path, int ram27_size_words, const char *ram28_hier_path, int ram28_size_words, const char *ram29_hier_path, int ram29_size_words, const char *ram30_hier_path, int ram30_size_words, const char *ram31_hier_path, int ram31_size_words, const char *ram32_hier_path, int ram32_size_words )
    : _ram1(ram1_hier_path, ram1_size_words, 4),
      _ram2(ram2_hier_path, ram2_size_words, 4),
      _ram3(ram3_hier_path, ram3_size_words, 4),
      _ram4(ram4_hier_path, ram4_size_words, 4),
      _ram5(ram5_hier_path, ram5_size_words, 4),
      _ram6(ram6_hier_path, ram6_size_words, 4),
      _ram7(ram7_hier_path, ram7_size_words, 4),
      _ram8(ram8_hier_path, ram8_size_words, 4),
      _ram9(ram9_hier_path, ram9_size_words, 4),
      _ram10(ram10_hier_path, ram10_size_words, 4),
      _ram11(ram11_hier_path, ram11_size_words, 4),
      _ram12(ram12_hier_path, ram12_size_words, 4),
      _ram13(ram13_hier_path, ram13_size_words, 4),
      _ram14(ram14_hier_path, ram14_size_words, 4),
      _ram15(ram15_hier_path, ram15_size_words, 4),
      _ram16(ram16_hier_path, ram16_size_words, 4),
      _ram17(ram17_hier_path, ram17_size_words, 4),
      _ram18(ram18_hier_path, ram18_size_words, 4),
      _ram19(ram19_hier_path, ram19_size_words, 4),
      _ram20(ram20_hier_path, ram20_size_words, 4),
      _ram21(ram21_hier_path, ram21_size_words, 4),
      _ram22(ram22_hier_path, ram22_size_words, 4),
      _ram23(ram23_hier_path, ram23_size_words, 4),
      _ram24(ram24_hier_path, ram24_size_words, 4),
      _ram25(ram25_hier_path, ram25_size_words, 4),
      _ram26(ram26_hier_path, ram26_size_words, 4),
      _ram27(ram27_hier_path, ram27_size_words, 4),
      _ram28(ram28_hier_path, ram28_size_words, 4),
      _ram29(ram29_hier_path, ram29_size_words, 4),
      _ram30(ram30_hier_path, ram30_size_words, 4),
      _ram31(ram31_hier_path, ram31_size_words, 4),
      _ram32(ram32_hier_path, ram32_size_words, 4) {}

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
  std::cout << "RAM5" << std::endl;
  _memutil.RegisterMemoryArea("ram5", 0x00500000, &_ram5);
  std::cout << _ram5.GetSizeBytes() << std::endl;
  std::cout << "RAM6" << std::endl;
  _memutil.RegisterMemoryArea("ram6", 0x00600000, &_ram6);
  std::cout << _ram6.GetSizeBytes() << std::endl;
  std::cout << "RAM7" << std::endl;
  _memutil.RegisterMemoryArea("ram7", 0x00700000, &_ram7);
  std::cout << _ram7.GetSizeBytes() << std::endl;
  std::cout << "RAM8" << std::endl;
  _memutil.RegisterMemoryArea("ram8", 0x00800000, &_ram8);
  std::cout << _ram8.GetSizeBytes() << std::endl;
  std::cout << "RAM9" << std::endl;
  _memutil.RegisterMemoryArea("ram9", 0x00900000, &_ram9);
  std::cout << _ram9.GetSizeBytes() << std::endl;
  std::cout << "RAM10" << std::endl;
  _memutil.RegisterMemoryArea("ram10", 0x00A00000, &_ram10);
  std::cout << _ram10.GetSizeBytes() << std::endl;
  std::cout << "RAM11" << std::endl;
  _memutil.RegisterMemoryArea("ram11", 0x00B00000, &_ram11);
  std::cout << _ram11.GetSizeBytes() << std::endl;
  std::cout << "RAM12" << std::endl;
  _memutil.RegisterMemoryArea("ram12", 0x00C00000, &_ram12);
  std::cout << _ram12.GetSizeBytes() << std::endl;
  std::cout << "RAM13" << std::endl;
  _memutil.RegisterMemoryArea("ram13", 0x00D00000, &_ram13);
  std::cout << _ram13.GetSizeBytes() << std::endl;
  std::cout << "RAM14" << std::endl;
  _memutil.RegisterMemoryArea("ram14", 0x00E00000, &_ram14);
  std::cout << _ram14.GetSizeBytes() << std::endl;
  std::cout << "RAM15" << std::endl;
  _memutil.RegisterMemoryArea("ram15", 0x00F00000, &_ram15);
  std::cout << _ram15.GetSizeBytes() << std::endl;
  std::cout << "RAM16" << std::endl;
  _memutil.RegisterMemoryArea("ram16", 0x01000000, &_ram16);
  std::cout << _ram16.GetSizeBytes() << std::endl;
  std::cout << "RAM17" << std::endl;
  _memutil.RegisterMemoryArea("ram17", 0x01100000, &_ram17);
  std::cout << _ram17.GetSizeBytes() << std::endl;
  std::cout << "RAM18" << std::endl;
  _memutil.RegisterMemoryArea("ram18", 0x01200000, &_ram18);
  std::cout << _ram18.GetSizeBytes() << std::endl;
  std::cout << "RAM19" << std::endl;
  _memutil.RegisterMemoryArea("ram19", 0x01300000, &_ram19);
  std::cout << _ram19.GetSizeBytes() << std::endl;
  std::cout << "RAM20" << std::endl;
  _memutil.RegisterMemoryArea("ram20", 0x01400000, &_ram20);
  std::cout << _ram20.GetSizeBytes() << std::endl;
  std::cout << "RAM21" << std::endl;
  _memutil.RegisterMemoryArea("ram21", 0x01500000, &_ram21);
  std::cout << _ram21.GetSizeBytes() << std::endl;
  std::cout << "RAM22" << std::endl;
  _memutil.RegisterMemoryArea("ram22", 0x01600000, &_ram22);
  std::cout << _ram22.GetSizeBytes() << std::endl;
  std::cout << "RAM23" << std::endl;
  _memutil.RegisterMemoryArea("ram23", 0x01700000, &_ram23);
  std::cout << _ram23.GetSizeBytes() << std::endl;
  std::cout << "RAM24" << std::endl;
  _memutil.RegisterMemoryArea("ram24", 0x01800000, &_ram24);
  std::cout << _ram24.GetSizeBytes() << std::endl;
  std::cout << "RAM25" << std::endl;
  _memutil.RegisterMemoryArea("ram25", 0x01900000, &_ram25);
  std::cout << _ram25.GetSizeBytes() << std::endl;
  std::cout << "RAM26" << std::endl;
  _memutil.RegisterMemoryArea("ram26", 0x01A00000, &_ram26);
  std::cout << _ram26.GetSizeBytes() << std::endl;
  std::cout << "RAM27" << std::endl;
  _memutil.RegisterMemoryArea("ram27", 0x01B00000, &_ram27);
  std::cout << _ram27.GetSizeBytes() << std::endl;
  std::cout << "RAM28" << std::endl;
  _memutil.RegisterMemoryArea("ram28", 0x01C00000, &_ram28);
  std::cout << _ram28.GetSizeBytes() << std::endl;
  std::cout << "RAM29" << std::endl;
  _memutil.RegisterMemoryArea("ram29", 0x01D00000, &_ram29);
  std::cout << _ram29.GetSizeBytes() << std::endl;
  std::cout << "RAM30" << std::endl;
  _memutil.RegisterMemoryArea("ram30", 0x01E00000, &_ram30);
  std::cout << _ram30.GetSizeBytes() << std::endl;
  std::cout << "RAM31" << std::endl;
  _memutil.RegisterMemoryArea("ram31", 0x01F00000, &_ram31);
  std::cout << _ram31.GetSizeBytes() << std::endl;
  std::cout << "RAM32" << std::endl;
  _memutil.RegisterMemoryArea("ram32", 0x02000000, &_ram32);
  std::cout << _ram32.GetSizeBytes() << std::endl;
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