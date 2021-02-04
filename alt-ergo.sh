#!/bin/bash
file=$1
res=$(alt-ergo ${file%.p}.smt2)
echo ${res}