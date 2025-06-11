#!/usr/bin/env python3
import argparse
import sys

def generate_multicore_system(num_rams: int) -> str:
    """
    Generate the C++ source code for a MulticoreSystem class
    with a constructor and Setup() method parameterized for num_rams.
    """
    # Header includes (unchanged)
    lines = [
        "// Copyright lowRISC contributors. Add commentMore actions",
        "// Licensed under the Apache License, Version 2.0, see LICENSE for details.",
        "// SPDX-License-Identifier: Apache-2.0",
        "",
        "#include <cassert>",
        "#include <fstream>",
        "#include <iostream>",
        "",
        "#include \"Vibex_multicore_system__Syms.h\"",
        "#include \"ibex_pcounts.h\"",
        "#include \"ibex_multicore_system.h\"",
        "#include \"verilated_toplevel.h\"",
        "#include \"verilator_memutil.h\"",
        "#include \"verilator_sim_ctrl.h\"",
        "",
    ]

    # Build constructor signature
    ctor_params = []
    for i in range(1, num_rams + 1):
        ctor_params.append(f"const char *ram{i}_hier_path")
        ctor_params.append(f"int ram{i}_size_words")
    ctor_signature = (
        "MulticoreSystem::MulticoreSystem("
        + ", ".join(ctor_params)
        + " )"
    )
    lines.append(ctor_signature)

    # Build initializer list
    init_lines = []
    for i in range(1, num_rams + 1):
        init_lines.append(f"_ram{i}(ram{i}_hier_path, ram{i}_size_words, 4)")
    if init_lines:
        lines.append("    : " + ",\n      ".join(init_lines) + " {}")
    else:
        lines.append("    {}  // No RAMs specified")

    lines.append("")  # blank line

    # Main() remains unchanged
    lines.extend([
        "int MulticoreSystem::Main(int argc, char **argv) {",
        "  bool exit_app;",
        "  int ret_code = Setup(argc, argv, exit_app);",
        "",
        "  if (exit_app) {",
        "    return ret_code;",
        "  }",
        "",
        "  Run();",
        "  //RunCores();",
        "",
        "  if (!Finish()) {",
        "    return 1;",
        "  }",
        "",
        "  return 0;",
        "}",
        ""
    ])

    # GetIsaString() unchanged
    lines.extend([
        "std::string MulticoreSystem::GetIsaString() const {",
        "  const Vibex_multicore_system &top = _top;",
        "  assert(top.ibex_multicore_system);",
        "",
        "  std::string base = top.ibex_multicore_system->RV32E ? \"rv32e\" : \"rv32i\";",
        "",
        "  std::string extensions;",
        "  if (top.ibex_multicore_system->RV32M)",
        "    extensions += \"m\";",
        "",
        "  extensions += \"c\";",
        "",
        "  switch (top.ibex_multicore_system->RV32B) {",
        "    case 0:  // RV32BNone",
        "      break;",
        "",
        "    case 1:  // RV32BBalanced",
        "      extensions += \"_Zba_Zbb_Zbs_XZbf_XZbt\";",
        "      break;",
        "",
        "    case 2:  // RV32BOTEarlGrey",
        "      extensions += \"_Zba_Zbb_Zbc_Zbs_XZbf_XZbp_XZbr_XZbt\";",
        "      break;",
        "",
        "    case 3:  // RV32BFull",
        "      extensions += \"_Zba_Zbb_Zbc_Zbs_XZbe_XZbf_XZbp_XZbr_XZbt\";",
        "      break;",
        "  }",
        "",
        "  return base + extensions;",
        "}",
        ""
    ])

    # Setup(): parameterized registration of each RAM
    lines.append("int MulticoreSystem::Setup(int argc, char **argv, bool &exit_app) {")
    lines.append("  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();")
    lines.append("")
    lines.append("  simctrl.SetTop(&_top, &_top.IO_CLK, &_top.IO_RST_N,")
    lines.append("                 VerilatorSimCtrlFlags::ResetPolarityNegative);")
    lines.append("")
    # Register each RAM in order, assigning base addresses spaced by 0x00200000
    base_address = 0x00100000
    stride = 0x00100000
    for i in range(1, num_rams + 1):
        addr_hex = f"0x{base_address + (i-1) * stride:08X}"
        lines.append(f"  std::cout << \"RAM{i}\" << std::endl;")
        lines.append(f"  _memutil.RegisterMemoryArea(\"ram{i}\", {addr_hex}, &_ram{i});")
        lines.append("  std::cout << _ram{i}.GetSizeBytes() << std::endl;".replace("{i}", str(i)))
    lines.append("  simctrl.RegisterExtension(&_memutil);")
    lines.append("")
    lines.append("  exit_app = false;")
    lines.append("  return simctrl.ParseCommandArgs(argc, argv, exit_app);")
    lines.append("}")
    lines.append("")

    # Run() unchanged
    lines.extend([
        "void MulticoreSystem::Run() {",
        "  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();",
        "",
        "  std::cout << \"Simulation of Ibex\" << std::endl",
        "            << \"==================\" << std::endl",
        "            << std::endl;",
        "",
        "  simctrl.RunSimulation();",
        "}",
        ""
    ])

    # Finish() unchanged
    lines.extend([
        "bool MulticoreSystem::Finish() {",
        "  VerilatorSimCtrl &simctrl = VerilatorSimCtrl::GetInstance();",
        "",
        "  if (!simctrl.WasSimulationSuccessful()) {",
        "    return false;",
        "  }",
        "",
        "  // Set the scope to the root scope, the ibex_pcount_string function otherwise",
        "  // doesn't know the scope itself. Could be moved to ibex_pcount_string, but",
        "  // would require a way to set the scope name from here, similar to MemUtil.",
        "  svSetScope(svGetScopeFromName(\"TOP.ibex_multicore_system\"));",
        "",
        "  std::cout << \"\\nPerformance Counters\" << std::endl",
        "            << \"====================\" << std::endl;",
        "  std::cout << ibex_pcount_string(false);",
        "",
        "  std::ofstream pcount_csv(\"ibex_multicore_system_pcount.csv\");",
        "  pcount_csv << ibex_pcount_string(true);",
        "",
        "  return true;",
        "}"
    ])

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate a C++ source file for MulticoreSystem with a variable number of RAMs."
    )
    parser.add_argument(
        "num_rams",
        type=int,
        help="Number of RAM instances to generate (must be >= 1)."
    )
    parser.add_argument(
        "output_file",
        help="Output filename (e.g., multicore_system.cpp) where the generated code will be written."
    )
    args = parser.parse_args()

    if args.num_rams < 1:
        print("Error: num_rams must be at least 1.", file=sys.stderr)
        sys.exit(1)

    cpp_code = generate_multicore_system(args.num_rams)
    try:
        with open(args.output_file, "w") as f:
            f.write(cpp_code)
        print(f"Generated C++ code with {args.num_rams} RAM(s) to '{args.output_file}'.")
    except IOError as e:
        print(f"Error writing to file '{args.output_file}': {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
