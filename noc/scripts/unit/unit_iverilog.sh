#!/bin/bash
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_iverilog.sh credit_bp_rx_tb
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

SV2V_OUTPUT=${TB}_sv2v.v

OUTPUT_WAVES=${UNIT_OUT_DIR}/${TB}_iverilog.fst
OUTPUT_WAVES_VCD=${UNIT_OUT_DIR}/${TB}_iverilog.vcd
THREADS=`nproc`
FILELIST=${UNIT_SCRIPT_DIR}/$TB.f

####################################################################################################
# Script Logic
####################################################################################################

rm -f ${OUTPUT_WAVES}
rm -f ${UNIT_OUT_DIR}/${TB}_iverilog.log
rm -rf ${UNIT_OUT_DIR}/${TB}_iverilog
mkdir -p ${UNIT_OUT_DIR}
mkdir -p ${UNIT_OUT_DIR}/${TB}_iverilog
cd ${UNIT_OUT_DIR}/${TB}_iverilog
ln -s ${REPO_ROOT}/rtl/* ./
ln -s ${REPO_ROOT}/rtl/experiment/* ./
ln -s ${REPO_ROOT}/rtl/topologies/* ./
ln -s ${REPO_ROOT}/includes/* ./
ln -s ${REPO_ROOT}/verif/* ./
ln -s ${REPO_ROOT}/verif/unit/* ./
ln -s ${REPO_ROOT}/verif/client/* ./

SOURCES=`cat $FILELIST`

cat > iverilog_top.sv << EOF
module iverilog_top;
    ${TB} tb ();

    initial begin
        \$dumpfile("${OUTPUT_WAVES}");
        \$dumpvars(0, iverilog_top.tb);
    end
endmodule
EOF

#TODO set SIMULATION once iverilog supports concurrent assertions
echo "Doing SV2V conversion..." | tee ${UNIT_OUT_DIR}/${TB}_iverilog.log
sv2v $SOURCES $TB.sv iverilog_top.sv -DIVERILOG -DREPO_ROOT=$REPO_ROOT --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=iverilog_top > ${SV2V_OUTPUT} | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log
#sv2v $SOURCES $TB.sv iverilog_top.sv -DIVERILOG -DREPO_ROOT=$REPO_ROOT -DSIMULATION --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=iverilog_top > ${SV2V_OUTPUT} | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

echo "Elaborating $TB..." | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log
iverilog -g2012 -gsupported-assertions -DREPO_ROOT=$REPO_ROOT -DSIMULATION -o $TB.out ${SV2V_OUTPUT} | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

echo "Simulating $TB..." | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log
vvp $TB.out -fst | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

#Return failure if an assertion fired
grep ERROR -vqz ${UNIT_OUT_DIR}/${TB}_iverilog.log | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

#Perform verif client checks (if applicable)
${UNIT_SCRIPT_DIR}/verif_client_check.sh ${UNIT_OUT_DIR}/${TB}_iverilog.log | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

#Collect stats
${REPO_ROOT}/scripts/results/stats.sh ${UNIT_OUT_DIR}/${TB}_iverilog.log ${UNIT_OUT_DIR}/${TB}_iverilog.csv | tee -a ${UNIT_OUT_DIR}/${TB}_iverilog.log

#Also convert the waves to VCD
#Actually don't do this, this ends up being WAY too big
#fst2vcd -f $OUTPUT_WAVES -o $OUTPUT_WAVES_VCD
