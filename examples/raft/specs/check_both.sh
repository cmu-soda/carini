#!/bin/sh

java -jar /Users/idardik/bin/tla2tools.jar -deadlock -workers 8 check.tla
java -jar /Users/idardik/bin/tla2tools.jar -deadlock -workers 8 check_bi.tla
