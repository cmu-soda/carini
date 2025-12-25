#/bin/sh

#/usr/bin/time -a -o out.log java -jar ../../../../bin/carini.jar C1.tla Cache.cfg T1.tla no_invs.cfg none --universal --sym-actions 8 --workers 10 --neg-trace-check 200 --pos-trace-check 3 --heap 10G >out.log 2>out.err &
/usr/bin/time -a -o out.log java -jar ../../../../bin/carini.jar C1.tla Cache.cfg Cache.tla no_invs.cfg none --universal --sym-actions 8 --workers 10 --neg-trace-check 200 --pos-trace-check 3 --heap 10G >out.log 2>out.err &
