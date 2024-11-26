#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=12
export FSYNTH_MAX_FORMULA_SIZE=8

/usr/bin/time -a -o stdout.log java -jar ../../../bin/assump-synth.jar T2.tla no_invs.cfg C3.tla no_invs.cfg C1.inv \
C2.tla no_invs.cfg \
C4.tla no_invs.cfg \
T4.tla no_invs.cfg >stdout.log 2>stderr.log
