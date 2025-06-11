#!/usr/bin/env python3

import os
import subprocess
import sys
import shutil
from pathlib import Path

def main():
    print("Starting sv2v conversion...")
    
    # Create output directory
    output_dir = Path("sv2v_output")
    if output_dir.exists():
        shutil.rmtree(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # List of SystemVerilog files to convert
    sv_files = [
        "noc/rtl/common_pkg.sv",
        "noc/rtl/noc_if.sv", 
        "noc/rtl/noc_pipe.sv",
        "noc/rtl/pi_switch_top.sv",
        "noc/rtl/t_switch_top.sv",
        "noc/rtl/axis_if.sv",
        "noc/rtl/axis_noc_bridge.sv",
        "noc/rtl/credit_bp_rx.sv",
        "noc/rtl/credit_bp_tx.sv",
        "noc/rtl/fifo32.sv",
        "noc/rtl/matrix_arbiter.sv",
        "noc/rtl/mux.sv",
        "noc/rtl/pi_route.sv",
        "noc/rtl/pi_switch.sv",
        "noc/rtl/t_route.sv",
        "noc/rtl/t_switch.sv",
        "noc/rtl/topologies/topology_pi_rectangle.sv",
        "noc/rtl/topologies/topology_t_binary_tree.sv",
        "rtl/ibex_multicore_system.sv"
    ]
    
    # Include files to copy (not convert)
    include_files = [
        ("noc/includes/system.h", "sv2v_output/noc/includes/system.h"),
        ("noc/includes/mux.h", "sv2v_output/noc/includes/mux.h"), 
        ("noc/includes/commands.h", "sv2v_output/noc/includes/commands.h")
    ]
    
    # Copy include files
    print("Copying include files...")
    for src, dst in include_files:
        if os.path.exists(src):
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)
            print(f"  Copied: {src} -> {dst}")
    
    # Convert SystemVerilog files
    print("Converting SystemVerilog files...")
    for sv_file in sv_files:
        if not os.path.exists(sv_file):
            print(f"Warning: File not found: {sv_file}")
            continue
            
        # Calculate output path
        rel_path = sv_file.replace(".sv", ".v")
        output_file = output_dir / rel_path
        
        # Create output directory
        output_file.parent.mkdir(parents=True, exist_ok=True)
        
        # Run sv2v conversion
        try:
            print(f"  Converting: {sv_file} -> {output_file}")
            
            # Run sv2v with include directories
            cmd = [
                "sv2v",
                "--include-dir=noc/includes",
                "--include-dir=noc/rtl", 
                sv_file
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            
            # Write converted output
            with open(output_file, 'w') as f:
                f.write(result.stdout)
                
        except subprocess.CalledProcessError as e:
            print(f"Error converting {sv_file}: {e}")
            print(f"stderr: {e.stderr}")
            return 1
        except Exception as e:
            print(f"Unexpected error converting {sv_file}: {e}")
            return 1
    
    print("sv2v conversion completed successfully!")
    return 0

if __name__ == "__main__":
    sys.exit(main())