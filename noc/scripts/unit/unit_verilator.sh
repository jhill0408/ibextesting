#!/bin/bash
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_verilator.sh credit_bp_rx_tb
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TB=$1
if [ -z "$2" ]; then
    SV2V_VERILATOR=0
else
    SV2V_VERILATOR=$2
fi

REPO_ROOT=`git rev-parse --show-toplevel`
UNIT_SCRIPT_DIR=${REPO_ROOT}/scripts/unit
UNIT_TB_DIR=${REPO_ROOT}/tb/unit
UNIT_OUT_DIR=${REPO_ROOT}/results/unit

SV2V_OUTPUT=${TB}_verilator_sv2v.sv

OUTPUT_WAVES=${UNIT_OUT_DIR}/${TB}_verilator.fst
OUTPUT_WAVES_VCD=${UNIT_OUT_DIR}/${TB}_verilator.vcd
THREADS=`nproc`
WRAPPER=${UNIT_SCRIPT_DIR}/unit_verilator_wrapper.cpp
FILELIST=${UNIT_SCRIPT_DIR}/$TB.f

####################################################################################################
# Script Logic
####################################################################################################

rm -f ${OUTPUT_WAVES}
rm -f ${UNIT_OUT_DIR}/${TB}_verilator.log
rm -rf ${UNIT_OUT_DIR}/${TB}_verilator
mkdir -p ${UNIT_OUT_DIR}
mkdir -p ${UNIT_OUT_DIR}/${TB}_verilator
cd ${UNIT_OUT_DIR}/${TB}_verilator
ln -s ${REPO_ROOT}/rtl/* ./
ln -s ${REPO_ROOT}/rtl/experiment/* ./
ln -s ${REPO_ROOT}/rtl/topologies/* ./
ln -s ${REPO_ROOT}/includes/* ./
ln -s ${REPO_ROOT}/verif/* ./
ln -s ${REPO_ROOT}/verif/unit/* ./
ln -s ${REPO_ROOT}/verif/client/* ./
ln -s ${WRAPPER} ./

SOURCES=`cat $FILELIST`
SOURCES="$SOURCES $TB.sv"

if [[ $SV2V_VERILATOR == "1" ]]; then
    echo "SV2V_VERILATOR set: Doing SV2V conversion..." | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log
    sv2v $SOURCES -DVERILATOR -DREPO_ROOT=$REPO_ROOT -DSIMULATION --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=$TB > ${SV2V_OUTPUT}
    SOURCES=${SV2V_OUTPUT}
fi

echo "Building simulator binary $TB.elf..." | tee ${UNIT_OUT_DIR}/${TB}_verilator.log
verilator \
    --exe --build --timing \
    --build-jobs $THREADS --threads $THREADS \
    +1800-2012ext+sv -sv -Wall -Wno-fatal -cc --assert \
    --trace-threads 2 --trace-structs --trace-fst \
    -DREPO_ROOT=$REPO_ROOT -DSIMULATION \
    --top-module $TB \
    $SOURCES \
    -CFLAGS -fcoroutines \
    -CFLAGS -DSV_TBENCH_NAME=$TB -CFLAGS -DVERILATED_CLASS=V$TB -CFLAGS -DVERILATED_HEADER=\"V$TB.h\" -CFLAGS -DWAVES_OUTPUT_PATH=$OUTPUT_WAVES \
    $WRAPPER \
    -o $TB.elf 2>&1 | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log

if [[ $SV2V_VERILATOR != "1" ]]; then
    #Skip these extra checks if we're using SV2V since it introduces a bunch of them...
    echo "Checking for build problems..." | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log

    #Return failure if there was a warning or error during the build
    grep "Error" -vqz ${UNIT_OUT_DIR}/${TB}_verilator.log | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log
    grep "Warning" -vqz ${UNIT_OUT_DIR}/${TB}_verilator.log | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log
fi

echo "Running $TB.elf..." | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log
./obj_dir/$TB.elf 2>&1 | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log

#Perform verif client checks (if applicable)
${UNIT_SCRIPT_DIR}/verif_client_check.sh ${UNIT_OUT_DIR}/${TB}_verilator.log | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log

#Collect stats
${REPO_ROOT}/scripts/results/stats.sh ${UNIT_OUT_DIR}/${TB}_verilator.log ${UNIT_OUT_DIR}/${TB}_verilator.csv | tee -a ${UNIT_OUT_DIR}/${TB}_verilator.log

#Also convert the waves to VCD
#Actually don't do this, this ends up being WAY too big
#fst2vcd -f $OUTPUT_WAVES -o $OUTPUT_WAVES_VCD
