#!/bin/bash

provers=(
"../zenon_modpol/zenon_modulo -brwrt -modulo -modulo-heuri -itptp -max-time 300s"
"../zenon_modpol/zenon_modulo -brwrt -x arith -modulo -modulo-heuri -itptp -max-time 300s"
)
prover_names=(
	zp
	zp+arith
	z3
	altergo
	)
res=""
filep=$1.p
filesmt=$1.smt2
filewhy=$1.why
for ((i=0; i < ${#provers[@]}; i++))
do
	prover=${provers[$i]}
	prover_name=${prover_names[$i]}
	f=$filep
	if [ "$prover_name" = "z3" ] 
	then f=$filesmt
	elif [ "$prover_name" = "altergo" ]
	then f=$filewhy
	fi
	t1=`date +%s%N`
	if $prover $f &> /dev/null; then
		t2=`date +%s%N`
		dt=`expr $t2 - $t1`
		dt=`expr $dt / 1000000`
		res="$res,\n \"$prover_name\": "$dt\ms""
	else res="$res,\n \"$prover_name\": -1"
	fi
done
echo -e "\"$1\": { ${res[@]:1} \n },"


