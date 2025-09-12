#/bin/sh

#export FSYNTH_MAX_NUM_WORKERS=12
#export FSYNTH_MAX_FORMULA_SIZE=8
export FSYNTH_NEG_TRACE_TIMEOUT=60

java -jar ../../../bin/carini.jar Log.tla no_invs.cfg StateTermConfig.tla no_invs.cfg Committed.inv
#/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar Log.tla no_invs.cfg T2.tla no_invs.cfg Committed.inv --ext-negt #>stdout.log 2>stderr.log
