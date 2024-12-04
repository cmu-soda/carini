#!/bin/sh

rm -f ii_out.log

for i in $(seq 1 50)
do
    echo "trial $i"
    #java -jar ~/bin/tla2tools.jar -deadlock -workers 10 -config D1_ii.cfg D1.tla | tee -a ii_out.log
    java -jar ~/bin/tla2tools.jar -deadlock -workers 10 -config client_server_db_ae_ii.cfg client_server_db_ae.tla | tee -a ii_out.log
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
grep 'Finished computing initial states: ' ii_out.log | sort | uniq -c
