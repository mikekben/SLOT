#!/bin/bash

#FILE=simplified.smt2
SMT_TIMEOUT=1

#../../slot/main -i aix -s $1

./slot/main -m -pall -s $1 -o opt-version.smt2 > /dev/null
#z3 opt-version.smt2

PRE_SOL_OUT=$( { z3 $1 -T:$SMT_TIMEOUT; } 2>&1 )
if [[ "$PRE_SOL_OUT" == "timeout" ]]
then
    echo "good"
else
    echo "bad"
fi
z3 opt-version.smt2

