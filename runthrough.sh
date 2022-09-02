#!/bin/bash
CLANG_FLAGS=$(cat passes-16.txt)
OPT_CMD=opt
Z3=z3
BOOLECTOR=boolector
CVC5=cvc5

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
        PYTHON_TIMEOUT=${OPTARG}
        ;;
    f)
        FILE=${OPTARG}
        ;;
  esac
done

#SMT_TIMEOUT=300
#PYTHON_TIMEOUT=300

#echo "$FILE"
NAME="${FILE%.*}"

FT_GOOD=true
OPT_GOOD=true
BK_GOOD=true

S1_SIZE=$(($(wc -c < "$FILE")))
#echo "Running frontend ..."
FRONTEND_OUT=$( { /usr/bin/time -f "tmr%e" timeout $PYTHON_TIMEOUT python3 frontend.py -s $FILE -o $NAME.ll; } 2>&1 > /dev/null )
if [[ $? == 124 ]]
then
    FT_GOOD=false
    FT_TIME=$PYTHON_TIMEOUT
else
    FT_TIME=$(echo "$FRONTEND_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
fi
#Check for unsupported floating point files
if [[ "$FRONTEND_OUT" == *"Unsupported floating point type"* ]]
then
    echo "$FILE,UnsupportedFP"
    exit
fi

if $FT_GOOD
then
    L1_SIZE=$(($(wc -c < "$NAME.ll")))
    #echo "Running optimizer ..."
    OPT_OUT=$( { /usr/bin/time -f "tmr%e" timeout $PYTHON_TIMEOUT $OPT_CMD $NAME.ll $CLANG_FLAGS -S -o $NAME-opt.ll; } 2>&1 > /dev/null )
    if [[ $? == 124 ]]
    then
        OPT_GOOD=false
        OPT_TIME=$PYTHON_TIMEOUT
    else
        OPT_TIME=$(echo "$OPT_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        #Remove attributes since the LLVM parser doesn't support the newer ones
        sed -i '/attributes/d' $NAME-opt.ll
        L2_SIZE=$(($(wc -c < "$NAME-opt.ll")))

        #echo "Running backend ..."
        BACKEND_OUT=$( { /usr/bin/time -f "tmr%e" timeout $PYTHON_TIMEOUT python3 backend.py -s -l $NAME-opt.ll -o $NAME-opt.smt2; } 2>&1 > /dev/null)
        if [[ $? == 124 ]]
        then
            BK_GOOD=false
            BK_TIME=$PYTHON_TIMEOUT
        else
            BK_TIME=$(echo "$BACKEND_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
            S2_SIZE=$(($(wc -c < "$NAME-opt.smt2")))
        fi
    fi  
fi



#Z3----------------
if $USE_Z3
then
    PRE_SOL_OUT=$($Z3 -smt2 $FILE -st -T:$SMT_TIMEOUT)
    PRE_SOL_OUT=$( { /usr/bin/time -f "tmr%e" $Z3 $FILE -T:$SMT_TIMEOUT; } 2>&1 )
    if [[ "$PRE_SOL_OUT" == "timeout" ]]
    then
        Z3_PRE_TIME=$SMT_TIMEOUT
        Z3_PRE_RESULT="timeout"
    else
        Z3_PRE_TIME=$(echo "$PRE_SOL_OUT" | grep -Po 'tmr*.*' | tr -dc '.0-9')
        Z3_PRE_RESULT=$(echo $PRE_SOL_OUT | awk '{print $1;}')
    fi

    if $FT_GOOD && $OPT_GOOD && $BK_GOOD
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

    if $FT_GOOD && $OPT_GOOD && $BK_GOOD
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

    if $FT_GOOD && $OPT_GOOD && $BK_GOOD
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

echo "$FILE,$S1_SIZE,$L1_SIZE,$L2_SIZE,$S2_SIZE,$FT_TIME,$OPT_TIME,$BK_TIME,$Z3_PRE_RESULT,$Z3_PRE_TIME,$Z3_POST_RESULT,$Z3_POST_TIME,$CV_PRE_RESULT,$CV_PRE_TIME,$CV_POST_RESULT,$CV_POST_TIME,$BL_PRE_RESULT,$BL_PRE_TIME,$BL_POST_RESULT,$BL_POST_TIME"

if $CLEANUP
then
rm $NAME.ll
rm $NAME-opt.ll
rm $NAME-opt.smt2
fi



