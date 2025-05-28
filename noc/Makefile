#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.

.PHONY: help
help:
	@echo "Available make targets:"
	@echo "    help:                 Print this help text!"
	@echo "    run_func_demo:        Run the functional demo"
	@echo "    run_hw_mapping:       Run the hardware mapping demo"
	@echo "    run_hw_mapping_fp:    Run the hardware mapping demo with floating point"
	@echo "    run_hw_mapping_ooc:   Do an out-of-context Vivado synthesis run on a subset of the hardware"
	@echo "    run_hw_mapping_yosys: Do Yosys synthesis run on a subset of the hardware"
	@echo "    run_unit_verilator:   Run a unit test with Verilator"
	@echo "    run_unit_iverilog:    Run a unit test with Icarus Verilog"
	@echo "    run_unit_xsim:        Run a unit test with XSim"
	@echo "    run_verilator_sweep:  Run a sweep of Verilator topologies"

run_func_demo:
	@cd scripts/results && \
	sh test.sh 1 ${TOPO} ${PE} ${RATE} ${TRACE} 

run_hw_mapping:
	@cd scripts/xilinx && \
	sh bft_synth.sh 1 ${TOPO} ${PE} ${DW} 

run_hw_mapping_fp:
	@cd scripts/xilinx && \
	sh bft_synth_fp.sh 1 ${TOPO} ${PE} ${DW} 

run_hw_mapping_ooc:
	bash scripts/xilinx/out_of_context/ooc_synth.sh ${NAME}

run_hw_mapping_yosys:
	bash scripts/yosys/yosys_synth.sh ${NAME}

run_unit_verilator:
	bash scripts/unit/unit_verilator.sh ${TB} ${SV2V_VERILATOR}
	gtkwave results/unit/${TB}_verilator.fst

run_unit_iverilog:
	bash scripts/unit/unit_iverilog.sh ${TB}
	gtkwave results/unit/${TB}_iverilog.fst

run_unit_xsim:
	bash scripts/unit/unit_xsim.sh ${TB}
	xsim --gui results/unit/${TB}_xsim.wdb

run_verilator_sweep:
	cd verif/rust && cargo build --release
	verif/rust/target/release/sweep
