#/bin/sh

java -jar ~/bin/tla2tools.jar -cleanup -deadlock -workers auto -config neg_traces.cfg C3_hist.tla >tlc_stdout.log 2>tlc_stderr.log
