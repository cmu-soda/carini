#/bin/sh

#export FSYNTH_MAX_NUM_WORKERS=12
#export FSYNTH_MAX_FORMULA_SIZE=8
#export FSYNTH_NEG_TRACE_TIMEOUT=10

java -jar ../../../bin/carini.jar Committed.tla MongoStaticRaft.cfg LogStateTermConfig.tla no_invs.cfg none
#/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar Committed.tla MongoStaticRaft.cfg LogStateTermConfig.tla no_invs.cfg none #>stdout.log 2>stderr.log
