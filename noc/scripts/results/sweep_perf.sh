rm bp_bft.*
echo "sigma,topo,n,rate,pat,sent,recv,time_taken,injection_rate,sustained_rate,if_worst_latency,queue_cumu_worst_latency,sum_queueing,worst_total_latency,sa" > bp_bft.csv

parallel --progress --bar --resume-failed --joblog ./log --gnu -j8 --header : \
	'	
	sh test.sh {#} {TOPO} {N} {RATE} {PAT} '\
	::: TOPO XBAR \
	::: PAT random \
	::: N 64 \
	::: RATE 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 \
