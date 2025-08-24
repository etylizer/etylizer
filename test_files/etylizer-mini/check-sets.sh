#!/bin/bash
set -e

cd $(dirname $0)

# crashes:
# C1) map generator comprehension

# modifications :
# default record values: new/1
# overlays: from_list/1, union/2, intersection_decided/3, del_element/2

# errors:
# 1) type error
# 2) erlang does not have a type for tuple(T)

QF=""
QF=$QF" -i filter/2" # C1)
QF=$QF" -i map/2" # C1)
QF=$QF" -i is_element/2" # 1) transitive
QF=$QF" -i add_element/2" # 1) transitive
QF=$QF" -i del_element/2" # 1) transitive
QF=$QF" -i filtermap/2" # 1) folding over empty instatiation of new
QF=$QF" -i update_bucket/3" # 1) works only for version 1
QF=$QF" -i get_slot/2" # 1) only works for version 1
QF=$QF" -i get_bucket/2" # 1) only works for version 1
QF=$QF" -i maybe_expand/1" # 1) only works for version 1
QF=$QF" -i maybe_expand_segs/1" # 1) only works for version 1
QF=$QF" -i maybe_contract/2" # 1) only works for version 1
QF=$QF" -i maybe_contract_segs/1" # 1) only works for version 1
QF=$QF" -i fold_segs/4" # 2)
QF=$QF" -i fold_seg/4" # 2)
QF=$QF" -i filter_set/2" # 2)
QF=$QF" -i filter_seg_list/4" # 2)
QF=$QF" -i get_bucket_s/2" # 2)
QF=$QF" -i put_bucket_s/3" # 2)
../../ety --type-overlay overlay.erl --no-deps $QF -f -l info stdlib/sets2.erl

QF=" -i filter/2" # C1)
QF=$QF" -i map/2" # C1)
../../ety --report-mode report --report-timeout 190000 --type-overlay overlay.erl --no-deps $QF $EX -f stdlib/sets2.erl

