#!/bin/bash
set -e

cd $(dirname $0)

# 1) default record values
# 2) overlay needed
# 3) exhaustiveness (added) (maps iterator strangeness)
# 4) transitive type error from unprecise function application
# 5) type error
# 6) map generator comprehension
# 7) erlang does not have a type for tuple(T)
# 8) exhaustiveness invariant

QF=""
QF=$QF" -i new/1" # 8)
QF=$QF" -i from_list/1" # 2)
QF=$QF" -i union/2" # 2)
QF=$QF" -i intersection_decided/3" # 2)
QF=$QF" -i from_list/2" # 3)
QF=$QF" -i is_element/2" # 4)
QF=$QF" -i add_element/2" # 4)
QF=$QF" -i del_element/2" # 2) + 4)
QF=$QF" -i filtermap/2" # 5) folding over empty instatiation of new
QF=$QF" -i update_bucket/3" # 5) works only for version 1
QF=$QF" -i get_slot/2" # 5) only works for version 1
QF=$QF" -i get_bucket/2" # 5) only works for version 1
QF=$QF" -i maybe_expand/1" # 5) only works for version 1
QF=$QF" -i maybe_expand_segs/1" # 5) only works for version 1? TODO refinement?
QF=$QF" -i maybe_contract/2" # 5) only works for version 1
QF=$QF" -i maybe_contract_segs/1" # 5) only works for version 1
QF=$QF" -i filter/2" # 6)
QF=$QF" -i map/2" # 6)
QF=$QF" -i fold_segs/4" # 7)
QF=$QF" -i fold_seg/4" # 7)
QF=$QF" -i filter_set/2" # 7)
QF=$QF" -i filter_seg_list/4" # 7)
QF=$QF" -i get_bucket_s/2" # 7)
QF=$QF" -i put_bucket_s/3" # 7)
QF=$QF" -i subtract_decided/3" # 8)
QF=$QF" -i fold/3" # 8)
QF=$QF" -i rehash/4" # 8)
../../ety --type-overlay overlay.erl --no-deps $QF -f -l info stdlib/sets2.erl 

QF=" -i filter/2" # 6)
QF=$QF" -i map/2" # 6)
../../ety --report-mode report --report-timeout 3000 --type-overlay overlay.erl --no-deps $QF -f stdlib/sets2.erl 
