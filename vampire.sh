#!/bin/bash
file=$1
res=$(./vampire4.5.1 --proof off --input_syntax smtlib2 ${file%.p}.smt2 | grep "Termination reason:")
echo ${res:22}