#!/usr/bin/env python3
import argparse
import sys

def generate_main_cpp(num_rams: int) -> str:
    """
    Generate a C++ source file (main.cpp) that instantiates MulticoreSystem
    with a variable number of RAM arguments based on num_rams.
    """
    lines = [
        "// Copyright lowRISC contributors.Add commentMore actions",
        "// Licensed under the Apache License, Version 2.0, see LICENSE for details.",
        "// SPDX-License-Identifier: Apache-2.0",
        "",
        "#include \"ibex_multicore_system.h\"",
        "",
        "int main(int argc, char **argv) {",
        "  MulticoreSystem multicore_system(",
    ]

    # Generate each "<path>", <size> pair
    # Use the pattern from the 2-RAM example:
    #TOP.ibex_multicore_system.gen_rams[0].u_ram.u_ram.gen_generic.u_impl_generic
    # "TOP.ibex_multicore_system.u_ram<i>.u_ram.gen_generic.u_impl_generic", 1024*1024/4
    size_expr = "1024*1024/4"
    for i in range(1, num_rams + 1):
        path = f"\"TOP.ibex_multicore_system.gen_rams[{i-1}].u_ram.u_ram.gen_generic.u_impl_generic\""
        size = size_expr
        # Append comma except after the last pair
        comma = "," if i < num_rams else ""
        lines.append(f"      {path}, {size}{comma}")

    lines.append("  );")
    lines.append("")
    lines.append("  return multicore_system.Main(argc, argv);")
    lines.append("}")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate a main.cpp that instantiates MulticoreSystem with N RAMs."
    )
    parser.add_argument(
        "num_rams",
        type=int,
        help="Number of RAM instances to pass into the MulticoreSystem constructor (>=1)."
    )
    parser.add_argument(
        "output_file",
        help="Output filename (e.g., main.cpp) for the generated C++ code."
    )
    args = parser.parse_args()

    if args.num_rams < 1:
        print("Error: num_rams must be at least 1.", file=sys.stderr)
        sys.exit(1)

    cpp_content = generate_main_cpp(args.num_rams)
    try:
        with open(args.output_file, "w") as f:
            f.write(cpp_content + "\n")
        print(f"Generated main.cpp with {args.num_rams} RAM(s) to '{args.output_file}'.")
    except IOError as e:
        print(f"Error writing to file '{args.output_file}': {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
