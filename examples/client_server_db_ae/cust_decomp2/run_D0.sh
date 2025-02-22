#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=15
export FSYNTH_MAX_FORMULA_SIZE=8

java -jar ../../../bin/assump-synth.jar D0.tla client_server_db_ae.cfg D1.tla no_invs.cfg none 1
