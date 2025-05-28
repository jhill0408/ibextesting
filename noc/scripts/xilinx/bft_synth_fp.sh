#!/bin/zsh

TOPO=$2
CLIENTS=$3
DW=$4
#vivado='alias /opt/Xilinx/Vivado/2017.4/bin/vivado'
if [ "$TOPO" = "BFT0" ]; then
    TOPO_bp=TREE
elif [ "$TOPO" = "BFT1" ]; then
    TOPO_bp=MESH0
elif [ "$TOPO" = "BFT2" ]; then
    TOPO_bp=MESH1
elif [ "$TOPO" = "BFT3" ]; then
    TOPO_bp=XBAR
fi
python3 split.py $CLIENTS >> top.xdc
rm -rf ../../results/hw_mapping/fc_bft_area.*
rm -rf ../../results/hw_mapping/fc_bft_freq.*
rm -rf ../../results/hw_mapping/fc_bft_power.*
echo "n,topo,dw,sa,dynamic,total" >> ../../results/hw_mapping/fc_bft_power.csv
echo "n,topo,dw,luts,ffs" >> ../../results/hw_mapping/fc_bft_area.csv
echo "n,topo,dw,clk_period" >> ../../results/hw_mapping/fc_bft_freq.csv
rm -rf ../../vivado
mkdir ../../vivado
cd ../../vivado
mkdir bft
cd bft
rm -rf *		
sed -i "6s?.*?parameter\ D_W=${DW},?" ../../rtl/bft_synth.v
#echo "create_project TOP -part xcvu9p-flga2104-3-e" > test.tcl
echo "create_project TOP -part xc7z007sclg400-1" > test.tcl
echo "add_files -norecurse {../../rtl/common_pkg.sv ../../rtl/axis_if.sv ../../rtl/noc_if.sv ../../rtl/bft_synth.v ../../rtl/mux.v ../../rtl/t_switch_top.v ../../rtl/t_switch.v ../../rtl/t_route.v ../../rtl/bp.v ../../rtl/axis_noc_bridge.sv ../../rtl/noc_pipe.sv}" >> test.tcl
echo "add_files -norecurse { ../../includes/commands.h ../../includes/mux.h ../../includes/system.h}" >> test.tcl
echo "add_files -norecurse { ../../rtl/pi_switch_top.v ../../rtl/pi_route.v ../../rtl/pi_switch.v}" >> test.tcl
echo "add_files -fileset constrs_1 -norecurse ../../scripts/xilinx/top.xdc" >> test.tcl
echo "set_property verilog_define $TOPO_bp [current_fileset]" >> test.tcl
echo "update_compile_order -fileset sources_1" >> test.tcl
echo "update_compile_order -fileset sim_1" >> test.tcl
echo "set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} -value {-generic N=$CLIENTS D_W=$DW} -objects [get_runs synth_1]" >> test.tcl
echo "synth_design -generic N=$CLIENTS -generic D_W=$DW -mode out_of_context" >> test.tcl
echo "write_checkpoint -force -file design.dcp" >> test.tcl
echo "opt_design" >> test.tcl
echo "place_design" >> test.tcl
echo "route_design" >> test.tcl
echo "report_utilization -file ../../results/hw_mapping/fc_${TOPO}_area_$CLIENTS.txt" >> test.tcl
echo "report_timing_summary -file ../../results/hw_mapping/fc_${TOPO}_freq_$CLIENTS.txt" >> test.tcl
for SA in 10 20 30 40 50 100
do
	echo "set_switching_activity -static_probability 0.5 -toggle_rate $SA [get_nets *]" >> test.tcl
	echo "report_power -file ../../results/hw_mapping/fc_${TOPO}_power_${CLIENTS}_sa_${SA}.txt" >> test.tcl
done
echo "exit" >> test.tcl 
vivado -mode tcl -s test.tcl #> /dev/null
cd ../../results/hw_mapping/

slack=$(awk '/Design\ Timing\ Summary/{getline; getline; getline;getline;getline;getline;print}' fc_${TOPO}_freq_$CLIENTS.txt |awk '{print $1}') #'{print N=$CLIENTS,TOPO=$TOPO,SLACK=$1}'
luts=$(awk '/CLB\ LUTs/{print}' fc_${TOPO}_area_$CLIENTS.txt | cut -d"|" -f 3 | awk '{print $1}')
ffs=$(awk '/Register\ as\ Flip\ Flop/{print}' fc_${TOPO}_area_$CLIENTS.txt | cut -d"|" -f 3 | awk '{print $1}')

slack=$(echo $slack - 1 | bc)
cp=$(echo 1000/"(-1*${slack})" | bc)
rm fc_${TOPO}_freq_${CLIENTS}.txt
echo "N=$CLIENTS,TOPO=$TOPO,dw=$DW,slack=$slack" >> fc_bft_freq.txt
echo "$CLIENTS,fc_$TOPO,$DW,$slack" >> fc_bft_freq.csv
rm fc_${TOPO}_area_${CLIENTS}.txt
echo "N=$CLIENTS,TOPO=$TOPO,dw=$DW,luts=$luts,ffs=$ffs" >> fc_bft_area.txt
echo "$CLIENTS,fc_$TOPO,$DW,$luts,$ffs" >> fc_bft_area.csv
echo "*****************************"
echo "Topology=$TOPO, PE=$CLIENTS, DW=$DW"
echo "*****************************"
echo "Achievable Frequency (MHz) = $cp"
echo "FPGA LUTs Consumed = $luts"
echo "FPGA Flip Flops Consumed = $ffs"
for SA in 10 20 30 40 50 100
do
	total=$(awk '/Total\ On-Chip\ Power/{print}' fc_${TOPO}_power_${CLIENTS}_sa_${SA}.txt | cut -d "|" -f 3 | awk '{print $1}')
	dynamic=$(awk '/Dynamic\ \(W\)/{print}' fc_${TOPO}_power_${CLIENTS}_sa_${SA}.txt | cut -d "|" -f 3 | awk '{print $1}')
	rm fc_${TOPO}_power_${CLIENTS}_sa_${SA}.txt
	echo "N=$CLIENTS,TOPO=fc_$TOPO,dw=$DW,SA=$SA,DYNAMIC=$dynamic,TOTAL=$total" >> fc_bft_power.txt
	echo "$CLIENTS,fc_$TOPO,$DW,$SA,$dynamic,$total" >> fc_bft_power.csv
	echo "Total Power (W) = $total Dynamic Power (W) = $dynamic (rate=$SA)"
done
