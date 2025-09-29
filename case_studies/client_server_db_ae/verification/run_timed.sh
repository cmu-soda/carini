#!/bin/bash

num_runs=5

total_time=0
max_time=0

for i in $(seq 1 $num_runs)
do
    # run_ServerDB.sh
    start=$(date +%s.%N)
    ./run_ServerDB.sh >/dev/null 2>&1
    end=$(date +%s.%N)
    elapsed=$(echo "$end - $start" | bc)
    total_time=$(echo "$total_time + $elapsed" | bc)
    greater=$(echo "$elapsed > $max_time" | bc)
    if [ "$greater" -eq 1 ]; then
        max_time=$elapsed
    fi
    echo "ServerDB run $i: $elapsed seconds"
done

avg=$(echo "scale=4; $total_time / $num_runs" | bc)
echo "Average time for run_ServerDB.sh: $avg seconds"
echo "Max time for run_ServerDB.sh: $max_time seconds"

../../cleanup.sh
