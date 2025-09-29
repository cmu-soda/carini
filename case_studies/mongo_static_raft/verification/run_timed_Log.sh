#!/bin/bash

num_runs=5

total_time=0
max_time=0

for i in $(seq 1 $num_runs)
do
    # run_Log.sh
    start=$(date +%s.%N)
    ./run_Log.sh >/dev/null 2>&1
    end=$(date +%s.%N)
    elapsed=$(echo "$end - $start" | bc)
    total_time=$(echo "$total_time + $elapsed" | bc)
    greater=$(echo "$elapsed > $max_time" | bc)
    if [ "$greater" -eq 1 ]; then
        max_time=$elapsed
    fi
    echo "Log run $i: $elapsed seconds"
done

avg=$(echo "scale=4; $total_time / $num_runs" | bc)
echo "Average time for run_Log.sh: $avg seconds"
echo "Max time for run_Log.sh: $max_time seconds"

rm -f CexTrace.* cextrace.txt *_hist.* formula_infer_* pos_traces.cfg neg_traces.cfg
rm -rf states/
