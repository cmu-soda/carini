#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8
export FSYNTH_NEG_TRACE_TIMEOUT=120

/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar \
	C3_inc.tla no_invs.cfg T2.tla no_invs.cfg MongoStaticRaft.tla MongoStaticRaft.cfg C1_inc.inv #>stdout.log 2>stderr.log
