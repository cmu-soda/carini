#/bin/sh

export FSYNTH_MAX_NUM_WORKERS=15
export FSYNTH_MAX_FORMULA_SIZE=8

java -jar ../../../bin/carini.jar Server.tla client_server_db_ae.cfg DB.tla no_invs.cfg none --naive
