#!/bin/zsh

# count metrics for bandwidth
packets_sent=`wc -l sent.log | cut -d" " -f 1`
packets_recv=`wc -l recv.log | cut -d" " -f 1`
time_taken=`cat test.log | grep -v "are done" | tail -n 2 | head -n 1 | sed "s/Time\(.*\):.*/\1/"`
ir=`cat test.log | grep "RATE=" | sed "s/RATE=\(.*\),.*/\1/"`
n=`cat test.log | grep "N=" | sed "s/.*N=//"`

# count metrics for latency
cat test.log | grep "Attempted" | cut -d" " -f1,3 | sed "s/Time//" | sed "s/://" | sed "s/packetid=//" | sort -t" " -k2 -V | sed "s/ /,/" > attempt.log
cat test.log | grep "Sent" | cut -d" " -f1,9 | sed "s/Time//" | sed "s/://" | sed "s/\(.*\),/\1/" | sed "s/packetid=//" | sort -t" " -k2 -V | sed "s/ /,/" > sentq.log
cat test.log | grep "Received" | cut -d" " -f1,7 | sed "s/Time//" | sed "s/://" | sed "s/\(.*\),/\1/" | sed "s/data=//" | sort -t" " -k2 -V | sed "s/ /,/" > recvq.log
paste -d"," attempt.log sentq.log recvq.log > latency.log

awk -F"," '{print $5-$1","$5-$3","$3-$1}' latency.log > latency-fixed.log
total_latency=`cat latency-fixed.log | cut -d"," -f 1 | numsum`
queue_worst_latency=`cat latency-fixed.log | cut -d"," -f 3 | numbound`
if_worst_latency=`cat latency-fixed.log | cut -d"," -f 2 | numbound`
sum_queueing=`cat latency-fixed.log | cut -d"," -f 3 | numsum`
worst_total_latency=`cat latency-fixed.log | cut -d"," -f 1 | numbound`
average_latency=$(echo $total_latency/$packets_sent | bc -l)
irtxt=`echo "scale=3; $ir/100" | bc -l`
ortxt=`echo "scale=3; $packets_sent/($time_taken*$n)" | bc -l`
echo " "
echo " Packets Sent = ${packets_sent}, Packets Recieved = ${packets_recv}"
echo " "
echo " Cycles = ${time_taken},  NoC sustained Rate = ${ortxt}"
echo " "
echo " Worst Inflight Latency = ${if_worst_latency}, Worst Total Latency = ${worst_total_latency}"
