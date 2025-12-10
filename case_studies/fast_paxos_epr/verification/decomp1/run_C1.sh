#/bin/sh

#export FSYNTH_NEG_TRACE_TIMEOUT=60
java -jar ../../../../bin/carini.jar C1.tla fast_paxos_epr.cfg T1.tla no_invs.cfg none --sym-actions 8
