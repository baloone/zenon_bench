#!/bin/bash

provers=(
"../zenon_modpol/zenon_modulo -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -modsko -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -modsko -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -modsko -modminiscope -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -modsko -modminiscope -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -modsko -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -modsko -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -modsko -modminiscope -modulo -modulo-heuri -itptp -max-time 1h"
"../zenon_modpol/zenon_modulo -x arith -modsko -modminiscope -brwrt -modulo -modulo-heuri -itptp -max-time 1h"
)
prover_names=(
	zp
	zp+brwrt
	zp+sko
	zp+brwrt+sko
	zp+sko+mini
	zp+brwrt+sko+mini
	zp+arith
	zp+brwrt+arith
	zp+sko+arith
	zp+brwrt+sko+arith
	zp+sko+mini+arith
	zp+brwrt+sko+mini+arith
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
		res="$res, \"$prover_name\": $dt"
	else res="$res, \"$prover_name\": -1"
	fi
done
echo "\"$1\": { ${res[@]:1} },"


