#!/bin/bash
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: yosys_synth.sh fifo32

set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

NAME=$1

REPO_ROOT=`git rev-parse --show-toplevel`
YOSYS_SCRIPT_DIR=${REPO_ROOT}/scripts/yosys
YOSYS_RESULT_DIR=${REPO_ROOT}/results/hw_mapping/yosys
SV2V_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_sv2v.v
YOSYS_VERILOG_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_netlist.v
YOSYS_EDIF_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_netlist.edif
YOSYS_BLIF_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_netlist.blif
YOSYS_PRE_SYNTH_SCHEMATIC_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_pre_synth
YOSYS_POST_SYNTH_SCHEMATIC_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}_post_synth
YOSYS_LOG_OUTPUT=${YOSYS_RESULT_DIR}/${NAME}.log

FILELIST=${YOSYS_SCRIPT_DIR}/$NAME.f
SOURCES=`cat $FILELIST`

####################################################################################################
# The Inner Goodness
####################################################################################################

printf "Running Yosys synthesis for ${NAME}\n"
rm -f ${SV2V_OUTPUT}
rm -f ${YOSYS_VERILOG_OUTPUT}
rm -f ${YOSYS_EDIF_OUTPUT}
rm -f ${YOSYS_BLIF_OUTPUT}
rm -f ${YOSYS_LOG_OUTPUT}
rm -f ${YOSYS_PRE_SYNTH_SCHEMATIC_OUTPUT}*
rm -f ${YOSYS_POST_SYNTH_SCHEMATIC_OUTPUT}*
rm -rf ${YOSYS_RESULT_DIR}/${NAME}_synth
mkdir -p ${YOSYS_RESULT_DIR}
mkdir -p ${YOSYS_RESULT_DIR}/${NAME}_synth
cd ${YOSYS_RESULT_DIR}/${NAME}_synth
ln -s ${REPO_ROOT}/rtl/* ./
ln -s ${REPO_ROOT}/rtl/experiment/* ./
ln -s ${REPO_ROOT}/rtl/topologies/* ./
ln -s ${REPO_ROOT}/includes/* ./

sv2v $SOURCES --top=$NAME > ${SV2V_OUTPUT}

cat > yosys_synth_script.ys << EOF
read -sv ${SV2V_OUTPUT}

hierarchy -check -top ${NAME}
show -prefix ${YOSYS_PRE_SYNTH_SCHEMATIC_OUTPUT} -format dot -viewer true
#show -prefix ${YOSYS_PRE_SYNTH_SCHEMATIC_OUTPUT} -format svg -viewer true

synth_xilinx -family xcup -top ${NAME} -retime
#synth_xilinx -family xcup -top ${NAME} -retime -edif ${YOSYS_EDIF_OUTPUT} -blif ${YOSYS_BLIF_OUTPUT}

show -prefix ${YOSYS_POST_SYNTH_SCHEMATIC_OUTPUT} -format dot -viewer true
#show -prefix ${YOSYS_POST_SYNTH_SCHEMATIC_OUTPUT} -format svg -viewer true

write_verilog ${YOSYS_VERILOG_OUTPUT}

stat -tech xilinx
EOF

yosys -s yosys_synth_script.ys 2>&1 | tee ${YOSYS_LOG_OUTPUT}
