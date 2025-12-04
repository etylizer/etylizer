#!/bin/bash

cd $(dirname $0)
-
# added 2 missing type specs
../../ety --build --no-deps -l note -f stdlib/ordsets2.erl

# added 11 missing type specs
# 1) redundant branch at top-level 
# 2) imprecise spec
# 3) exhaustiveness at top-level
# 4) overlay for lists:reverse to add the nonempty_list -> nonempty_list case
QF=""
QF=$QF" -o new/0"
QF=$QF" -o is_queue/1"
QF=$QF" -i get/1" # 2)
QF=$QF" -o is_empty/1" # 1)
QF=$QF" -o len/1" # 1)
QF=$QF" -o to_list/1" # 1)
QF=$QF" -o from_list/1" # 1)
QF=$QF" -o member/2" # 1)
QF=$QF" -o in/2" # 1)
QF=$QF" -o in_r/2" # 1)
# QF=$QF" -o out/1" # 34 minutes
# QF=$QF" -o out_r/1" # 10 minutes
QF=$QF" -i get/2" # 2) 3)
QF=$QF" -o get_r/1" # 1)
QF=$QF" -o peek/1" # 1)
QF=$QF" -o peek_r/1" # 1)
QF=$QF" -o drop/1" # 4) 
QF=$QF" -o drop_r/1" # 4)
QF=$QF" -o reverse/1" # 1)
QF=$QF" -o join/2" # 1) 10s
# QF=$QF" -o split/2" # timeout
QF=$QF" -o split_f1_to_r2/5" # 3)
QF=$QF" -o split_r1_to_f2/5" # 3)
QF=$QF" -o filter/2"
# QF=$QF" -o filter_f/2" # 5 minutes
QF=$QF" -o filter_r/2"
QF=$QF" -o filtermap/2"
QF=$QF" -o filtermap_r/2"
QF=$QF" -o fold/3"
QF=$QF" -o any/2"
QF=$QF" -o all/2"
QF=$QF" -o delete/2" # 1)
QF=$QF" -o delete_r/2" # 1)
QF=$QF" -o delete_front/2"
QF=$QF" -o delete_rear/2" 
QF=$QF" -o delete_with/2"
QF=$QF" -o delete_with_r/2"
QF=$QF" -o delete_with_front/2"
QF=$QF" -o delete_with_rear/2"
QF=$QF" -o cons/2"
QF=$QF" -i head/1" # 2)
QF=$QF" -o tail/1"
QF=$QF" -o snoc/2"
QF=$QF" -o daeh/1"
QF=$QF" -o last/1"
QF=$QF" -o liat/1"
QF=$QF" -o lait/1"
QF=$QF" -o init/1"
QF=$QF" -o r2f/1"
QF=$QF" -o f2r/1"
../../ety --build --type-overlay overlay_queue.erl --no-deps -f -l note stdlib/queue2.erl $QF
