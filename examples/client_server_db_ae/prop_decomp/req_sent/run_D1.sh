#/bin/sh

java -jar ../../../../bin/recomp-verify.jar client_server_db_ae.tla client_server_db_ae.cfg D1.tla no_invs.cfg D0.inv \
E1.tla no_invs.cfg
