
#############
TOPO=$2
N=$3
RATE=$4
PAT=$5
SIGMA=$6

ID=${1}_${2}_${3}_${4}_${5}
cd bin/$ID
cp ../../result_skel.sh .

if [ "$TOPO" = "XBAR" ]; then
	pi_switches_ports=$(echo "l($N)/l(2)*(2*$N)" | bc -l)
	pi_switches_ports=$(echo ${pi_switches_ports%.*})
	t_switches_ports=0
elif [ "$TOPO" = "TREE" ]; then
	pi_switches_ports=0
	t_switches_ports=$(echo "($N-1)*3" | bc)
else
	pi_switches_ports=$(echo "l($N)/l(2)*($N)" | bc -l)
	t_switches_ports=$(echo "l($N)/l(2)*($N/4)*3" | bc -l)
fi

switching=`grep -nr "switching" test.log | wc -l`
time_taken=`cat test.log | grep -v "are done" | tail -n 2 | head -n 1 | sed "s/Time\(.*\):.*/\1/"`
sa=$(echo "${switching}/(${time_taken}*(${pi_switches_ports}+${t_switches_ports}))" | bc -l)
#echo $sa
##############
if [ "$TOPO" = "IC" ]; then
	echo "sem --id 0 echo TOPO=$TOPO, N=$N, RATE=$RATE, PAT=$PAT, sent=\$packets_sent, recv=\$packets_recv, time_taken=\$time_taken, injection_rate=\$irtxt, sustained rate=\$ortxt, if_worst_latency=\$if_worst_latency, queue_cumu_worst_latency=\$queue_worst_latency, sum_queueing=\$sum_queueing, worst_total_latency=\$worst_total_latency,SA=$sa >> ../../axi_ic.txt" >> result_skel.sh
	echo "sem --id 0 echo $TOPO,$N,$RATE,$PAT,\$packets_sent,\$packets_recv,\$time_taken,\$irtxt,\$ortxt,\$if_worst_latency,\$queue_worst_latency,\$sum_queueing,\$worst_total_latency,$sa,\$average_latency >> ../../axi_ic.csv" >> result_skel.sh

else
	echo "sem --id 0 echo TOPO=bp_$TOPO, N=$N, RATE=$RATE, PAT=$PAT, sent=\$packets_sent, recv=\$packets_recv, time_taken=\$time_taken, injection_rate=\$irtxt, sustained rate=\$ortxt, if_worst_latency=\$if_worst_latency, queue_cumu_worst_latency=\$queue_worst_latency, sum_queueing=\$sum_queueing, worst_total_latency=\$worst_total_latency,SA=$sa >> ../../../../results/perf/fc_bft.txt" >> result_skel.sh
    echo " ************************************************"
	echo " Topology=$TOPO, PE=$N, RATE=$RATE, TRACE=$PAT"
    echo " ************************************************"
    echo " Switching Activity=$sa" 
	echo "sem --id 0 echo $SIGMA,bp_$TOPO,$N,$RATE,$PAT,\$packets_sent,\$packets_recv,\$time_taken,\$irtxt,\$ortxt,\$if_worst_latency,\$queue_worst_latency,\$sum_queueing,\$worst_total_latency,$sa,\$average_latency >> ../../../../results/perf/fc_bft.csv" >> result_skel.sh
fi
chmod +x result_skel.sh
sh result_skel.sh
tar -zcf log.tar.gz *.log
find . ! -name 'log.tar.gz' -type f -exec rm -f {} +
#rm -rf *
