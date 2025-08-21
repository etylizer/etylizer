#!/bin/bash

cd $(dirname $0)

# ../../ety --build --no-deps -f -l info stdlib/ordsets2.erl

# 1) redundant branch at top-level 
# 2) imprecise spec
# 3) exhaustiveness at top-level
# 4) overlay for lists:reverse to add the nonempty_list -> nonempty_list case
QF=""
# QF=$QF" -o new/0"
# QF=$QF" -o is_queue/1"
# QF=$QF" -o get/1"
# QF=$QF" -o is_empty/1" # 1)
# QF=$QF" -o len/1" # 1)
# QF=$QF" -o to_list/1" # 1)
# QF=$QF" -o from_list/1" # 1)
# QF=$QF" -o member/2" # 1)
# QF=$QF" -o in/2" # 1)
# QF=$QF" -o in_r/2" # 1)
# # QF=$QF" -o out/1" # 34 minutes
QF=$QF" -o out_r/1" # 10 minutes
# QF=$QF" -o get/2" # 2) 3)
# QF=$QF" -o get_r/1" # 1)
# QF=$QF" -o peek/1" # 1)
# QF=$QF" -o peek_r/1" # 1)
# QF=$QF" -o drop/1" # 4) 
# QF=$QF" -o drop_r/1" # 4)
# QF=$QF" -o reverse/1" # 1)
# QF=$QF" -o join/2" # 1) 10s
# QF=$QF" -o split/2" # timeout
# QF=$QF" -o split_f1_to_r2/5" # 3)
# QF=$QF" -o split_r1_to_f2/5" # 3)
# QF=$QF" -o filter/2"
# QF=$QF" -o filter_f/2"
# QF=$QF" -o filter_r/2"
# QF=$QF" -o filtermap/2"
# QF=$QF" -o filtermap_r/2"
# QF=$QF" -o fold/3"
# QF=$QF" -o any/2"
# QF=$QF" -o all/2"
# QF=$QF" -o delete/2" # 1)
# QF=$QF" -o delete_r/2" # 1)
# QF=$QF" -o delete_front/2"
# QF=$QF" -o delete_rear/2" 
# QF=$QF" -o delete_with/2"
# QF=$QF" -o delete_with_r/2"
# QF=$QF" -o delete_with_front/2"
# QF=$QF" -o delete_with_rear/2"
# QF=$QF" -o cons/2"
# QF=$QF" -o head/1"
# QF=$QF" -o tail/1"
# QF=$QF" -o snoc/2"
# QF=$QF" -o daeh/1"
# QF=$QF" -o last/1"
# QF=$QF" -o liat/1"
# QF=$QF" -o lait/1"
# QF=$QF" -o init/1"
# QF=$QF" -o r2f/1"
# QF=$QF" -o f2r/1"


# 1) refinement on integer constraints
# 2) = operator exhaustiveness on lists
QF=""
# # QF=$QF" -o balance/1" # 1)
# QF=$QF" -o balance/2"
# QF=$QF" -o balance_list_1/2" # 1) 2) 
# QF=$QF" -o balance_list/2" # 2)
# QF=$QF" -o count/1"
# QF=$QF" -o delete_1/2"
# QF=$QF" -o delete/2"
# QF=$QF" -o delete_any/2"
# QF=$QF" -o empty/0"
# QF=$QF" -o enter/3"
# QF=$QF" -o from_orddict/1"
# QF=$QF" -o get_1/2"
# QF=$QF" -o get/2"
# QF=$QF" -o insert_1/4"
# QF=$QF" -o insert/3"
# QF=$QF" -o is_defined_1/2"
# QF=$QF" -o is_defined/2"
# QF=$QF" -o is_empty/1"
# QF=$QF" -o iterator/1"
# QF=$QF" -o iterator_1/2"
# QF=$QF" -o iterator/2"
# QF=$QF" -o iterator_from_1/3"
# QF=$QF" -o iterator_from/2"
# QF=$QF" -o iterator_from/3"
# QF=$QF" -o iterator_from_r/3"
# QF=$QF" -o iterator_r/2"
# QF=$QF" -o keys/1"
# QF=$QF" -o keys/2"
# QF=$QF" -o larger_1/2"
# QF=$QF" -o larger/2"
# QF=$QF" -o largest/1"
# QF=$QF" -o largest_1/1"
# QF=$QF" -o lookup_1/2"
# QF=$QF" -o lookup/2"
# QF=$QF" -o map_1/2"
# QF=$QF" -o map/2"
# QF=$QF" -o merge/2"
# QF=$QF" -o next/1"
# QF=$QF" -o size/1"
# QF=$QF" -o smaller_1/2"
# QF=$QF" -o smaller/2"
# QF=$QF" -o smallest/1"
# QF=$QF" -o smallest_1/1"
# QF=$QF" -o take_1/2"
# QF=$QF" -o take/2"
# QF=$QF" -o take_any/2"
# QF=$QF" -o take_largest/1"
# QF=$QF" -o take_largest1/1"
# QF=$QF" -o take_smallest/1"
# QF=$QF" -o take_smallest1/1"
# QF=$QF" -o to_list/1"
# QF=$QF" -o to_list_1/1"
# QF=$QF" -o to_list/2"
# QF=$QF" -o update_1/3"
# QF=$QF" -o update/3"
# QF=$QF" -o values/1"
# QF=$QF" -o values/2"
../../ety --build --no-deps -f -l debug stdlib/gb_trees2.erl $QF
