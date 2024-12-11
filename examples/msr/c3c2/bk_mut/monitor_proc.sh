#!/bin/bash

procs=(62001 62002)
outfile="/home/idardik/projects/compositional_ii/tla-sym-assump-synth/examples/msr/naive_decomp/mout.log"

date '+%A %W %Y %X' >> "$outfile"
echo "---------------------------" >> "$outfile"
free -g >> "$outfile"
echo "---------------------------" >> "$outfile"
df -h / >> "$outfile"
echo "---------------------------" >> "$outfile"
for proc in "${procs[@]}"
do
	ps x | grep "$proc" | grep -v grep >> "$outfile"
done
echo "---------------------------" >> "$outfile"
echo -e "\n" >> "$outfile"
