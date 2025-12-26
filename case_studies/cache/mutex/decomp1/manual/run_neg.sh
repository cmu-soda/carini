#!/bin/bash

java -jar ../../../../../bin/carini.jar --cex C1.tla neg_traces.cfg | sed 's/T[0-9]*->/\n/g' | tr -d '+()'
