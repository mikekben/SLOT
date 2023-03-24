#!/bin/bash
Z3=/nethome/bmikek3/z3/build/z3
BOOLECTOR=/nethome/bmikek3/boolector/build/bin/boolector
CVC5=/nethome/bmikek3/cvc5/build/bin/cvc5

TIMEOUT=300

FILE=$1
ORIG_TIME=$2


SLOT_OUT=$( { /usr/bin/time -f "tmr%e" timeout $ORIG_TIME ./slot -p -t slot-opts.csv -s $FILE -o $FILE-opt.smt2; } 2>&1 > /dev/null )
if [[ $? == 124 ]]
then
    SLOT_GOOD=false
    SLOT_TIME=$ORIG_TIME
else
    SLOT_TIME=$(echo "$SLOT_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
fi


#Z3----------------
Z3_OUT=$( { /usr/bin/time -f "tmr%e" $Z3 $FILE-opt.smt2 -T:$TIMEOUT; } 2>&1 )
#echo $Z3_OUT
if [[ "$Z3_OUT" == "timeout" ]]
then
    Z3_TIME=$TIMEOUT
    Z3_RESULT="timeout"
else
    Z3_TIME=$(echo "$Z3_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
    Z3_RESULT=$(echo $Z3_OUT | awk '{print $1;}')
fi



CV_OUT=$( { /usr/bin/time -f "tmr%e" $CVC5 $FILE-opt.smt2 -q  --tlimit=$(( 1000 * TIMEOUT )); } 2>&1 )
if [[ "$CV_OUT" == *"timeout"* ]]
then
    CV_TIME=$TIMEOUT
    CV_RESULT="timeout"
else
    CV_TIME=$(echo "$CV_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
    CV_RESULT=$(echo $CV_OUT | awk '{print $1;}')
fi


if [[ $FILE = ./QF_BV/* ]]
then
    BL_OUT=$( { /usr/bin/time -f "tmr%e" $BOOLECTOR $FILE-opt.smt2 -t $TIMEOUT; } 2>&1 )
    if [[ "$BL_OUT" == *"unknown"* ]]
    then
        BL_TIME=$TIMEOUT
        BL_RESULT="timeout"
    else
        BL_TIME=$(echo "$BL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        BL_RESULT=$(echo $BL_OUT | awk '{print $1;}')
    fi
else
    BL_TIME=""
    BL_RESULT=""
fi

#echo "$FILE,$Z3_RESULT,$Z3_TIME,$CV_RESULT,$CV_TIME,$BL_RESULT,$BL_TIME"
echo "$FILE,$SLOT_TIME,$Z3_RESULT,$Z3_TIME,$CV_RESULT,$CV_TIME,$BL_RESULT,$BL_TIME" >> slot_res.csv