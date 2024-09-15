#/bin/sh

time java -jar ../../../bin/assump-synth.jar MongoStaticRaft.tla MongoStaticRaft.cfg C1.tla MongoStaticRaft.cfg none \
C2.tla no_invs.cfg \
C3.tla no_invs.cfg \
C4.tla no_invs.cfg \
T4.tla no_invs.cfg >stdout.txt 2>stderr.txt
