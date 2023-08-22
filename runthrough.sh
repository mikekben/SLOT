#!/bin/bash
Z3=z3 #4.12.1
BOOLECTOR=boolector #3.2.2
CVC5=cvc5 #1.0.5

usage() { 
    echo "Usage: $0 [-r] [-z] [-c] [-b] [-f <file>]" 1>&2
    echo "   -r : Remove all produced files"
    echo "   -z : Use Z3 solver"
    echo "   -c : Use CVC5 solver"
    echo "   -b : Use Boolector solver"
    echo "   -t : Timeout (seconds)"
    echo "   -f : .smt2 file to process"
    exit 
}

FILE=""
STATS="slot-stats.csv"
CLEANUP=false
USE_Z3=false
USE_CV=false
USE_BL=false

while getopts "hrzcbt:f:" arg; do
  case $arg in
    h)
      usage
      ;;
    r)
      CLEANUP=true
      ;;
    z)
      USE_Z3=true
      ;;
    c)
      USE_CV=true
      ;;
    b)
      USE_BL=true
      ;;
    t)
        SMT_TIMEOUT=${OPTARG}
        SLOT_TIMEOUT=${OPTARG}
        ;;
    f)
        FILE=${OPTARG}
        ;;
  esac
done

#echo "$FILE"
NAME="${FILE%.*}"

SLOT_GOOD=true

#Check for timeout of SLOT
SLOT_OUT=$( { /usr/bin/time -f "tmr%e" timeout $SLOT_TIMEOUT ./main -m -pall -s $FILE -o $NAME-opt.smt2 -t $STATS; } 2>&1 > /dev/null )
if [[ $? == 124 ]]
then
    SLOT_GOOD=false
    echo "$FILE,Timeout" >> $STATS
fi


#Check for unsupported floating point files


#Encountered unsupported SMT type (Floating point type
#Encountered unsupported SMT operation (floating point rounding mode)


if [[ "$SLOT_OUT" == *"Encountered unsupported SMT type (floating point type"* ]]
then
    echo "$FILE,UnsupportedFPType"
    exit
fi

if [[ "$SLOT_OUT" == *"Encountered unsupported SMT operation (floating point rounding mode)"* ]]
then
    echo "$FILE,UnsupportedRoundingMode"
    exit
fi



#Z3----------------
if $USE_Z3
then
    PRE_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $Z3 $FILE -T:$SMT_TIMEOUT; } 2>&1 )
    if [[ "$PRE_SOL_OUT" == "timeout" ]]
    then
        Z3_PRE_TIME=$SMT_TIMEOUT
        Z3_PRE_RESULT="timeout"
    else
        Z3_PRE_TIME=$(echo "$PRE_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        Z3_PRE_RESULT=$(echo $PRE_SOL_OUT | awk '{print $1;}')
    fi

    if $SLOT_GOOD
    then
        POST_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $Z3 $NAME-opt.smt2 -T:$SMT_TIMEOUT; } 2>&1 )
        if [[ "$POST_SOL_OUT" == "timeout" ]]
        then
            Z3_POST_TIME=$SMT_TIMEOUT
            Z3_POST_RESULT="timeout"
        else
            Z3_POST_TIME=$(echo "$POST_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
            Z3_POST_RESULT=$(echo $POST_SOL_OUT | awk '{print $1;}')
        fi
    fi
fi


#------------------


#CVC5----------------
if $USE_CV
then
    PRE_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $CVC5 $FILE -q  --tlimit=$(( 1000 * SMT_TIMEOUT )); } 2>&1 )
    if [[ "$PRE_SOL_OUT" == *"timeout"* ]]
    then
        CV_PRE_TIME=$SMT_TIMEOUT
        CV_PRE_RESULT="timeout"
    else
        CV_PRE_TIME=$(echo "$PRE_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        CV_PRE_RESULT=$(echo $PRE_SOL_OUT | awk '{print $1;}')
    fi

    if $SLOT_GOOD
    then
        POST_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $CVC5 $NAME-opt.smt2 -q --tlimit=$(( 1000 * SMT_TIMEOUT )); } 2>&1 )
        if [[ "$POST_SOL_OUT" == *"timeout"* ]]
        then
            CV_POST_TIME=$SMT_TIMEOUT
            CV_POST_RESULT="timeout"
        else
            CV_POST_TIME=$(echo "$POST_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
            CV_POST_RESULT=$(echo $POST_SOL_OUT | awk '{print $1;}')
        fi
    fi
fi
#------------------


#BOOLECTOR----------------
if $USE_BL
then
    PRE_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $BOOLECTOR $FILE -t $SMT_TIMEOUT; } 2>&1 )
    if [[ "$PRE_SOL_OUT" == *"unknown"* ]]
    then
        BL_PRE_TIME=$SMT_TIMEOUT
        BL_PRE_RESULT="timeout"
    else
        BL_PRE_TIME=$(echo "$PRE_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        BL_PRE_RESULT=$(echo $PRE_SOL_OUT | awk '{print $1;}')
    fi

    if $SLOT_GOOD
    then
        POST_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $BOOLECTOR $NAME-opt.smt2 -t $SMT_TIMEOUT; } 2>&1 )
        if [[ "$POST_SOL_OUT" == *"unknown"* ]]
        then
            BL_POST_TIME=$SMT_TIMEOUT
            BL_POST_RESULT="timeout"
        else
            BL_POST_TIME=$(echo "$POST_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
            BL_POST_RESULT=$(echo $POST_SOL_OUT | awk '{print $1;}')
        fi
    fi
fi
#------------------

echo "$FILE,$Z3_PRE_RESULT,$Z3_PRE_TIME,$Z3_POST_RESULT,$Z3_POST_TIME,$CV_PRE_RESULT,$CV_PRE_TIME,$CV_POST_RESULT,$CV_POST_TIME,$BL_PRE_RESULT,$BL_PRE_TIME,$BL_POST_RESULT,$BL_POST_TIME"

if $CLEANUP
then
    rm $NAME-opt.smt2
fi



