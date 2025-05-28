#!/bin/sh
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Regression script run by Gitlab for yosys synthesis

#Setup
set -e
REPO_ROOT=`git rev-parse --show-toplevel`
cd $REPO_ROOT

#Invocations for several Yosys synthesis runs
#bash scripts/yosys/yosys_synth.sh credit_bp_rx#FIXME sv2v can't convert top-level modules with interface ports
#bash scripts/yosys/yosys_synth.sh credit_bp_tx#FIXME sv2v can't convert top-level modules with interface ports
bash scripts/yosys/yosys_synth.sh experiment_generic_mux2
bash scripts/yosys/yosys_synth.sh experiment_generic_mux3
bash scripts/yosys/yosys_synth.sh experiment_generic_mux4
bash scripts/yosys/yosys_synth.sh experiment_generic_mux6
bash scripts/yosys/yosys_synth.sh experiment_hier_mux_pi
bash scripts/yosys/yosys_synth.sh experiment_hier_mux_t
bash scripts/yosys/yosys_synth.sh experiment_mux4x2_mux6x2_pi
bash scripts/yosys/yosys_synth.sh experiment_mux4x3_t
bash scripts/yosys/yosys_synth.sh fifo32
bash scripts/yosys/yosys_synth.sh matrix_arbiter
#bash scripts/yosys/yosys_synth.sh noc_pipe#FIXME sv2v can't convert top-level modules with interface ports
bash scripts/yosys/yosys_synth.sh pi_route
bash scripts/yosys/yosys_synth.sh pi_switch
#bash scripts/yosys/yosys_synth.sh pi_switch_top#FIXME sv2v can't convert top-level modules with interface ports
bash scripts/yosys/yosys_synth.sh t_route
bash scripts/yosys/yosys_synth.sh t_switch
#bash scripts/yosys/yosys_synth.sh t_switch_top#FIXME sv2v can't convert top-level modules with interface ports
#bash scripts/yosys/yosys_synth.sh topology_t_binary_tree#FIXME sv2v can't convert top-level modules with interface ports
