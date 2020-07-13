#!/bin/bash

provers=(
~/zp/zenon_modulo\ -modulo\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zp/zenon_modulo\ -modulo\ -disable-skolem\ -disable-miniscoping\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zp/zenon_modulo\ -modulo\ -disable-miniscoping\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zp/zenon_modulo\ -x\ arith\ -modulo\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zp/zenon_modulo\ -x\ arith\ -modulo\ -disable-skolem\ -disable-miniscoping\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zp/zenon_modulo\ -x\ arith\ -modulo\ -disable-miniscoping\ -modulo-heuri\ -itptp\ -max-time\ 300s
~/zenon_modulo/zenon_modulo\ -modulo\ -modulo-heuri\ -itptp\ -max-time\ 300s
./z3.sh\ -smt2\ -T:300
alt-ergo\ -timelimit\ 300
)
prover_names=(
	zp
	zp-sko
	zp-mini
	zp+arith
	zp+arith-sko
	zp+arith-mini
	zm
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


