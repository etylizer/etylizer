#!/bin/bash

cd $(dirname $0)

QF=""
QF=$QF" -o new/0"
QF=$QF" -o is_queue/1"
QF=$QF" -o get/1"
# slowish
# QF=$QF" -o join/2" # 10s
# QF=$QF" -o split/2" # timeout
# failed exhaustiveness at top-level
QF=$QF" -o split_f1_to_r2/5"
# redundant branch at top-level 
# fun(...) ->
#   erlang:error(...).
QF=$QF" -o is_empty/1" 
QF=$QF" -o len/1"
QF=$QF" -o to_list/1"
QF=$QF" -o from_list/1"
QF=$QF" -o member/2"
QF=$QF" -o in/2"
QF=$QF" -o in_r/2"
QF=$QF" -o reverse/1"
# false positive: list granularity
# QF=$QF" -o out/1"
# QF=$QF" -o out_r/1"
# QF=$QF" -o get/2"
# QF=$QF" -o get_r/1"
# QF=$QF" -o peek/1"
# QF=$QF" -o peek_r/1"
# QF=$QF" -o drop/1"
# QF=$QF" -o drop_r/1"

#../../ety --build --no-deps -f -l debug stdlib/queue4.erl $QF
../../ety --build --no-deps -f -l debug stdlib/queue4.erl -o test
