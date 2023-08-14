#!/bin/bash

#FILE=simplified.smt2
#SMT_TIMEOUT=1

#../../slot/main -i aix -s $1

./main -m -pall -s $1 -o opt-version.smt2 > /dev/null

/nethome/bmikek3/boolector/build/bin/boolector $1
/nethome/bmikek3/boolector/build/bin/boolector opt-version.smt2

