#!/bin/bash
#########
TOPO=$2
N=$3
RATE=$4
PAT=$5
ID=${1}_${2}_${3}_${4}_${5}
##########

if [ "$TOPO" = "BFT0" ]; then
    TOPO_bp=0
elif [ "$TOPO" = "BFT1" ]; then
    TOPO_bp=2
elif [ "$TOPO" = "BFT2" ]; then
    TOPO_bp=3
elif [ "$TOPO" = "BFT3" ]; then
    TOPO_bp=1
fi

rm -rf bin/$ID
mkdir -p bin/$ID
cd bin/$ID
cp ../../../../rtl/* ./
cp ../../../../includes/* ./
cp -r ../../../../tb/* ./

if [ "$PAT" = "local" ]; then
	PARA_PAT=1
	TRACE=SYNTHETIC
elif [ "$PAT" = "random" ]; then
	PARA_PAT=0
	TRACE=SYNTHETIC
else
	PARA_PAT=0
	TRACE=REAL
	cp ../../../../bench/$PAT/$N/* ./
fi
if [ "$PAT" = "local" ]; then
	SIGMA_MAX=$(echo "sqrt($N)" | bc -l)
	SIGMA_MAX=$(echo ${SIGMA_MAX%.*})
	for SIGMA in $( seq 1 $SIGMA_MAX )
	do
		echo "Setting locality = "$SIGMA
		verilator -Wno-WIDTH -Wno-COMBDLY -Wno-WIDTHCONCAT -GTOPO=$TOPO_bp -D$TRACE -DSIM -GSIGMA=$SIGMA -GWRAP=1 -GN=$N -GRATE=$RATE -GPAT=$PARA_PAT --top-module bft --cc fifo32.sv common_pkg.sv axis_if.sv noc_if.sv bft.v client_bp.v client_bp_top.v mux.v pi_switch_top.v pi_switch.v t_switch.v t_route.v pi_route.v t_switch_top.v bp.v axis_noc_bridge.sv noc_pipe.sv --exe bft_tb.c > /dev/null
		make -C obj_dir -j -f Vbft.mk Vbft > /dev/null
		./obj_dir/Vbft > test.log
		cat test.log | grep "Sent" | cut -d" " -f 9 | sed "s/packetid=//" | sed "s/,//" | sort -V > sent.log
		cat test.log | grep "Received" | cut -d" " -f 7 | sed "s/data=//" | sed "s/,//" | sort -V > recv.log
		diff sent.log recv.log
		rm -rf obj_dir
		cd ../..
		sh perf.sh $1 $TOPO $N $RATE $PAT $SIGMA
		cd bin/$ID
		rm log.tar.gz
		cp ../../../../rtl/* ./
		cp ../../../../includes/* ./
		cp ../../../../tb/* ./
	done
else
##########
	verilator -Wno-WIDTH -Wno-COMBDLY -Wno-WIDTHCONCAT -GTOPO=$TOPO_bp -D$TRACE -DSIM -GWRAP=1 -GSIGMA=4 -GN=$N -GRATE=$RATE -GPAT=$PARA_PAT --top-module bft --cc fifo32.sv common_pkg.sv axis_if.sv noc_if.sv bft.v client_bp.v client_bp_top.v mux.v pi_switch_top.v pi_switch.v t_switch.v t_route.v pi_route.v t_switch_top.v bp.v axis_noc_bridge.sv noc_pipe.sv --exe bft_tb.c > /dev/null
	make -C obj_dir -j -f Vbft.mk Vbft > /dev/null
	./obj_dir/Vbft > test.log
	cat test.log | grep "Sent" | cut -d" " -f 9 | sed "s/packetid=//" | sed "s/,//" | sort -V > sent.log
	cat test.log | grep "Received" | cut -d" " -f 7 | sed "s/data=//" | sed "s/,//" | sort -V > recv.log
	diff sent.log recv.log
	#########
	rm -rf obj_dir
	cd ../..
	sh perf.sh $1 $TOPO $N $RATE $PAT
fi
