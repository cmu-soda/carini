#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8

#java -Xmx25G -jar ../../bin/assump-synth.jar ls_pending.tla no_invs.cfg ls_table.tla learning_switch.cfg none ls_pending.tla no_invs.cfg

/usr/bin/time -a -o stdout.log java -jar \
	../../bin/assump-synth.jar ls_table.tla learning_switch.cfg ls_pending.tla no_invs.cfg learning_switch.tla learning_switch.cfg none >stdout.log 2>stderr.log
