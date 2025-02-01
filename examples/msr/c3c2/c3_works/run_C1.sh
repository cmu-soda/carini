#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8
export FSYNTH_NEG_TRACE_TIMEOUT=10

/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar \
	C1.tla MongoStaticRaft.cfg T1.tla no_invs.cfg MongoStaticRaft.tla MongoStaticRaft.cfg none #>stdout.log 2>stderr.log
