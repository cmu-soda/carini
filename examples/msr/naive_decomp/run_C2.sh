#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=15

/usr/bin/time java -jar ../../../bin/assump-synth.jar MongoStaticRaft.tla MongoStaticRaft.cfg C2.tla no_invs.cfg C1.inv \
C3.tla no_invs.cfg \
C4.tla no_invs.cfg \
T4.tla no_invs.cfg
