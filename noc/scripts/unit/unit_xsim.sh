#!/bin/bash
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_xsim.sh credit_bp_rx_tb
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TB=$1

REPO_ROOT=`git rev-parse --show-toplevel`
UNIT_SCRIPT_DIR=${REPO_ROOT}/scripts/unit
UNIT_TB_DIR=${REPO_ROOT}/tb/unit
UNIT_OUT_DIR=${REPO_ROOT}/results/unit

THREADS=`nproc`
TCL=${UNIT_SCRIPT_DIR}/xsim.tcl
FILELIST=${UNIT_SCRIPT_DIR}/$TB.f

SNAPSHOT=snapshot_$TB
OUTPUT_WAVES_WDB=${UNIT_OUT_DIR}/${TB}_xsim.wdb
OUTPUT_WAVES_VCD=${UNIT_OUT_DIR}/${TB}_xsim.vcd

####################################################################################################
# Script Logic
####################################################################################################

rm -f ${OUTPUT_WAVES}
rm -f ${UNIT_OUT_DIR}/${TB}_xsim.log
rm -rf ${UNIT_OUT_DIR}/${TB}_xsim
mkdir -p ${UNIT_OUT_DIR}
mkdir -p ${UNIT_OUT_DIR}/${TB}_xsim
cd ${UNIT_OUT_DIR}/${TB}_xsim
ln -s ${REPO_ROOT}/rtl/* ./
ln -s ${REPO_ROOT}/rtl/experiment/* ./
ln -s ${REPO_ROOT}/rtl/topologies/* ./
ln -s ${REPO_ROOT}/includes/* ./
ln -s ${REPO_ROOT}/verif/* ./
ln -s ${REPO_ROOT}/verif/unit/* ./
ln -s ${REPO_ROOT}/verif/client/* ./
ln -s ${TCL} ./

SOURCES=`cat $FILELIST`

echo "Parsing (System)Verilog sources..." | tee ${UNIT_OUT_DIR}/${TB}_xsim.log
xvlog -d REPO_ROOT=$REPO_ROOT -d SIMULATION -d XSIM -sv $SOURCES $TB.sv | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log

echo "Elaborating design for simulation..." | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log
xelab -debug all -top $TB -snapshot $SNAPSHOT | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log

echo "Simulating design..." | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log
xsim $SNAPSHOT -tclbatch $TCL 2>&1 | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log

mv $SNAPSHOT.wdb $OUTPUT_WAVES_WDB
mv xsim_waves.vcd $OUTPUT_WAVES_VCD

#Return failure if an assertion fired
#Either "Error: Assertion violation" or "ERROR: Assertion failed."
grep "Assertion" -vqz ${UNIT_OUT_DIR}/${TB}_xsim.log | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log

#Perform verif client checks (if applicable)
${UNIT_SCRIPT_DIR}/verif_client_check.sh ${UNIT_OUT_DIR}/${TB}_xsim.log | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log

#Collect stats
${REPO_ROOT}/scripts/results/stats.sh ${UNIT_OUT_DIR}/${TB}_xsim.log ${UNIT_OUT_DIR}/${TB}_xsim.csv | tee -a ${UNIT_OUT_DIR}/${TB}_xsim.log
