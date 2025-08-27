#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8

#/usr/bin/time -a -o stdout.log java -jar ../../bin/assump-synth.jar ls_table.tla learning_switch.cfg ls_pending.tla no_invs.cfg none #>stdout.log 2>stderr.log
java -jar ../../bin/assump-synth.jar ls_table.tla learning_switch.cfg ls_pending.tla no_invs.cfg none #>stdout.log 2>stderr.log
