#!/bin/sh
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Regression script run by Gitlab
set -e

#unit_xsim.sh invocations for several testbenches
bash scripts/unit/unit_xsim.sh credit_bp_rx_tb
bash scripts/unit/unit_xsim.sh credit_bp_tx_tb
bash scripts/unit/unit_xsim.sh fifo32_tb
bash scripts/unit/unit_xsim.sh matrix_arbiter_tb
#bash scripts/unit/unit_xsim.sh mux_tb#Xsim straight up frees an invalid pointer and crashes hard when running this testbench lol
bash scripts/unit/unit_xsim.sh noc_pipe_tb
bash scripts/unit/unit_xsim.sh pi_route_tb
bash scripts/unit/unit_xsim.sh pi_simple_4_tb
bash scripts/unit/unit_xsim.sh pi_switch_tb
bash scripts/unit/unit_xsim.sh pi_switch_top_tb
bash scripts/unit/unit_xsim.sh t_binary_tree_3_tb
bash scripts/unit/unit_xsim.sh t_route_tb
bash scripts/unit/unit_xsim.sh t_switch_tb
bash scripts/unit/unit_xsim.sh t_switch_top_tb
bash scripts/unit/unit_xsim.sh verif_client_tb
bash scripts/unit/unit_xsim.sh topology_t_binary_tree_tb
bash scripts/unit/unit_xsim.sh topology_pi_rectangle_tb
bash scripts/unit/unit_xsim.sh topology_pi_rectangle_generalized_tb
