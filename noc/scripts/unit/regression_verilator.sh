#!/bin/sh
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Regression script run by Gitlab
set -e

#unit_verilator.sh invocations for several testbenches
#We use SV2V_VERILATOR for the picky testbenches
bash scripts/unit/unit_verilator.sh credit_bp_rx_tb
bash scripts/unit/unit_verilator.sh credit_bp_tx_tb
bash scripts/unit/unit_verilator.sh fifo32_tb
bash scripts/unit/unit_verilator.sh matrix_arbiter_tb
bash scripts/unit/unit_verilator.sh mux_tb
bash scripts/unit/unit_verilator.sh noc_pipe_tb
bash scripts/unit/unit_verilator.sh pi_route_tb
bash scripts/unit/unit_verilator.sh pi_simple_4_tb
bash scripts/unit/unit_verilator.sh pi_switch_tb
bash scripts/unit/unit_verilator.sh pi_switch_top_tb
bash scripts/unit/unit_verilator.sh t_binary_tree_3_tb
bash scripts/unit/unit_verilator.sh t_route_tb
bash scripts/unit/unit_verilator.sh t_switch_tb
bash scripts/unit/unit_verilator.sh t_switch_top_tb
bash scripts/unit/unit_verilator.sh verif_client_tb
bash scripts/unit/unit_verilator.sh topology_t_binary_tree_tb 1
bash scripts/unit/unit_verilator.sh topology_pi_rectangle_tb 1
bash scripts/unit/unit_verilator.sh topology_pi_rectangle_generalized_tb 1
