#!/bin/bash
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: ooc_synth.sh fifo32
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

NAME=$1

REPO_ROOT=`git rev-parse --show-toplevel`
OOC_RESULT_DIR=${REPO_ROOT}/results/hw_mapping/xilinx_ooc
OOC_SCRIPT_DIR=${REPO_ROOT}/scripts/xilinx/out_of_context

FILELIST=${OOC_SCRIPT_DIR}/$NAME.f
SOURCES=`cat $FILELIST`

####################################################################################################
# The Inner Goodness
####################################################################################################

printf "Running out-of-context synthesis for ${NAME}\n"
rm -f ${OOC_RESULT_DIR}/ooc_area_${NAME}.txt
rm -f ${OOC_RESULT_DIR}/ooc_freq_${NAME}.txt
rm -f ${OOC_RESULT_DIR}/ooc_power_${NAME}.txt
rm -f ${OOC_RESULT_DIR}/ooc_netlist_${NAME}.edif
rm -f ${OOC_RESULT_DIR}/ooc_netlist_${NAME}.v
rm -rf ${OOC_RESULT_DIR}/${NAME}_ooc_synth
mkdir -p ${OOC_RESULT_DIR}
mkdir -p ${OOC_RESULT_DIR}/${NAME}_ooc_synth
cd ${OOC_RESULT_DIR}/${NAME}_ooc_synth
ln -s ${REPO_ROOT}/rtl/* ./
ln -s ${REPO_ROOT}/rtl/experiment/* ./
ln -s ${REPO_ROOT}/rtl/topologies/* ./
ln -s ${REPO_ROOT}/includes/* ./

cat > vivado_ooc_synth_script.tcl << EOF
set OOC_RESULT_DIR ${REPO_ROOT}/results/hw_mapping/xilinx_ooc
set OOC_TCL_DIR ${REPO_ROOT}/scripts/xilinx/out_of_context

#create_project TOP -part xcvu9p-flga2104-3-e
create_project TOP -part xc7z007sclg400-1

add_files -norecurse {${SOURCES}}
add_files -fileset constrs_1 -norecurse ${REPO_ROOT}/scripts/xilinx/top.xdc

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

if { [catch {synth_design -mode out_of_context -top ${NAME} -lint}] } {
    puts "ERROR: Linting failed"
    exit 1
}

if { [catch {synth_design -mode out_of_context -top ${NAME}}] } {
    puts "ERROR: Synthesis failed"
    exit 1
}

if { [catch {opt_design} ]} {
    puts "ERROR: Optimization failed"
    exit 1
}

if { [catch {place_design}]} {
    puts "ERROR: Placement failed"
    exit 1
}

if { [catch {route_design}]} {
    puts "ERROR: Routing failed"
    exit 1
}

set_switching_activity -default_toggle_rate 100
report_power -file ../ooc_power_${NAME}.txt
report_utilization -file ../ooc_area_${NAME}.txt
report_timing_summary -file ../ooc_freq_${NAME}.txt
#write_edif ../ooc_netlist_${NAME}.edif
write_verilog ../ooc_netlist_${NAME}.v
exit
EOF

vivado -mode tcl -s vivado_ooc_synth_script.tcl 2>&1 | tee ${OOC_RESULT_DIR}/ooc_log_${NAME}.txt
