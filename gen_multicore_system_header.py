#!/usr/bin/env python3
import argparse
import sys

def generate_multicore_system_header(num_rams: int) -> str:
    """
    Generate the C++ header content for a MulticoreSystem class
    with a constructor and member declarations parameterized for num_rams.
    """
    lines = [
        "// Copyright lowRISC contributors.Add commentMore actions",
        "// Licensed under the Apache License, Version 2.0, see LICENSE for details.",
        "// SPDX-License-Identifier: Apache-2.0",
        "",
        "#include \"verilated_toplevel.h\"",
        "#include \"verilator_memutil.h\"",
        "",
        "class MulticoreSystem {",
        " public:",
    ]

    # Build constructor signature
    ctor_params = []
    for i in range(1, num_rams + 1):
        ctor_params.append(f"const char *ram{i}_hier_path")
        ctor_params.append(f"int ram{i}_size_words")
    ctor_signature = (
        "  MulticoreSystem("
        + ", ".join(ctor_params)
        + ");"
    )
    lines.append(ctor_signature)
    lines.append("  virtual ~MulticoreSystem() {}")
    lines.append("  virtual int Main(int argc, char **argv);")
    lines.append("")
    lines.append("  // Return an ISA string, as understood by Spike, for the system being")
    lines.append("  // simulated.")
    lines.append("  std::string GetIsaString() const;")
    lines.append("")
    lines.append(" protected:")
    lines.append("  ibex_multicore_system _top;")
    lines.append("  VerilatorMemUtil _memutil;")

    # Generate MemArea member variables
    for i in range(1, num_rams + 1):
        lines.append(f"  MemArea _ram{i};")

    lines.append("")
    lines.append("  virtual int Setup(int argc, char **argv, bool &exit_app);")
    lines.append("  virtual void Run();")
    lines.append("  //virtual void RunCores();")
    lines.append("  virtual bool Finish();")
    lines.append("};")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate a C++ header file for MulticoreSystem with a variable number of RAMs."
    )
    parser.add_argument(
        "num_rams",
        type=int,
        help="Number of RAM instances to generate (must be >= 1)."
    )
    parser.add_argument(
        "output_file",
        help="Output filename (e.g., multicore_system.h) where the generated header will be written."
    )
    args = parser.parse_args()

    if args.num_rams < 1:
        print("Error: num_rams must be at least 1.", file=sys.stderr)
        sys.exit(1)

    header_content = generate_multicore_system_header(args.num_rams)
    try:
        with open(args.output_file, "w") as f:
            f.write(header_content + "\n")
        print(f"Generated header with {args.num_rams} RAM(s) to '{args.output_file}'.")
    except IOError as e:
        print(f"Error writing to file '{args.output_file}': {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
