#/bin/sh

export FSYNTH_NEG_TRACE_TIMEOUT=60

java -jar ../../../bin/carini.jar Log.tla no_invs.cfg StateTermConfig.tla no_invs.cfg Committed.inv --naive
