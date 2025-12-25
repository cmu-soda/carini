#/bin/sh

/usr/bin/time -a -o out.log java -jar ../../../../bin/carini.jar C2.tla no_invs.cfg T2.tla no_invs.cfg C1.inv --universal --sym-actions 8 --workers 10 --neg-trace-check 200 --pos-trace-check 3 --heap 10G >out.log 2>out.err &
