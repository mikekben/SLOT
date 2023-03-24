#find ../../qfbv-big -type f -name '*.ll' -delete
#find ../../qfbv-big -type f -name '*-opt.smt2' -delete
#find . -name '*.smt2' -type f | parallel ./runthrough.sh
cat sorted_pre.csv | parallel ./wrapper.sh


#awk -F "\"*,\"*" '{print $1}' bv-errors.csv | parallel ./wrapper.sh >> bv-error-results.csv

#awk -F "\"*,\"*" '{print $1}' bv-errors.csv | parallel ./dd-sftest.sh >> is_segfault.txt
