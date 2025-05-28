#!/bin/sh
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Regression script run by Gitlab for out of context synthesis

#Setup
set -e
REPO_ROOT=`git rev-parse --show-toplevel`
cd $REPO_ROOT

#Invocations for several OOC synthesis runs
bash scripts/xilinx/out_of_context/ooc_synth.sh credit_bp_rx
bash scripts/xilinx/out_of_context/ooc_synth.sh credit_bp_tx
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_generic_mux2
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_generic_mux3
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_generic_mux4
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_generic_mux6
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_hier_mux_pi
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_hier_mux_t
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_mux4x2_mux6x2_pi
bash scripts/xilinx/out_of_context/ooc_synth.sh experiment_mux4x3_t
bash scripts/xilinx/out_of_context/ooc_synth.sh fifo32
bash scripts/xilinx/out_of_context/ooc_synth.sh matrix_arbiter
bash scripts/xilinx/out_of_context/ooc_synth.sh noc_pipe
bash scripts/xilinx/out_of_context/ooc_synth.sh pi_route
bash scripts/xilinx/out_of_context/ooc_synth.sh pi_switch
bash scripts/xilinx/out_of_context/ooc_synth.sh pi_switch_top
bash scripts/xilinx/out_of_context/ooc_synth.sh t_route
bash scripts/xilinx/out_of_context/ooc_synth.sh t_switch
bash scripts/xilinx/out_of_context/ooc_synth.sh t_switch_top
bash scripts/xilinx/out_of_context/ooc_synth.sh topology_t_binary_tree
