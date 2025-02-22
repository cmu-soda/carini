#!/bin/sh

rm -f ii_out.log

for i in $(seq 1 100)
do
    echo "trial $i"
    java -jar ~/bin/tla2tools.jar -cleanup -deadlock -workers auto -config C3_ii.cfg C3.tla | tee -a ii_out.log
    violations=$(grep 'Error: Invariant IndInv is violated.' ii_out.log | wc -l)
    if [ ${violations} -ne 0 ]
    then
        echo
        echo "violations were detected, the candidate is not an II!!"
        break
    fi
    echo
done

echo "no violations found, here is a summary of the run:"
grep 'Finished computing initial states: ' ii_out.log | sed 's/ at.*$//g' | sort | uniq -c
