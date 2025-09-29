#!/bin/bash

num_runs=5

RM_total_time=0
Env_total_time=0
RM_max_time=0
Env_max_time=0

for i in $(seq 1 $num_runs)
do
    # run_RM.sh
    start=$(date +%s.%N)
    ./run_RM.sh >/dev/null 2>&1
    end=$(date +%s.%N)
    elapsed=$(echo "$end - $start" | bc)
    RM_total_time=$(echo "$RM_total_time + $elapsed" | bc)
    greater=$(echo "$elapsed > $RM_max_time" | bc)
    if [ "$greater" -eq 1 ]; then
        RM_max_time=$elapsed
    fi
    echo "RM run $i: $elapsed seconds"

    # run_Env.sh
    start=$(date +%s.%N)
    ./run_Env.sh >/dev/null 2>&1
    end=$(date +%s.%N)
    elapsed=$(echo "$end - $start" | bc)
    Env_total_time=$(echo "$Env_total_time + $elapsed" | bc)
    greater=$(echo "$elapsed > $Env_max_time" | bc)
    if [ "$greater" -eq 1 ]; then
        Env_max_time=$elapsed
    fi
    echo "Env run $i: $elapsed seconds"
done

RM_avg=$(echo "scale=4; $RM_total_time / $num_runs" | bc)
Env_avg=$(echo "scale=4; $Env_total_time / $num_runs" | bc)
echo "Average time for run_RM.sh: $RM_avg seconds"
echo "Average time for run_Env.sh: $Env_avg seconds"
echo "Max time for run_RM.sh: $RM_max_time seconds"
echo "Max time for run_Env.sh: $Env_max_time seconds"

../../cleanup.sh
