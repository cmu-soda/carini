#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8

/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar \
	C3.tla no_invs.cfg T2.tla no_invs.cfg MongoStaticRaft.tla MongoStaticRaft.cfg C1.inv #>stdout.log 2>stderr.log
