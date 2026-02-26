#!/bin/bash
set -e

cd $(dirname $0)

# 1) requires {T, ...} types

QF=""
QF=$QF" -i expand/2" # 1)
QF=$QF" -i normalize/2" # 1)
QF=$QF" -i to_map/2" # 1)
QF=$QF" -i lookup/2" # 1)
QF=$QF" -i lookup_all/2" # 1)
QF=$QF" -i is_defined/3" # 1)
QF=$QF" -i get_all_value/2" # 1)
QF=$QF" -i append_values/2" # 1)
QF=$QF" -i get_bool/2" # 1)
QF=$QF" -i get_keys/2" # 1)
QF=$QF" -i delete/2" # 1)
QF=$QF" -i substitute_aliases_1/2" # 1)
QF=$QF" -i substitute_negations_1/2" # 1)
QF=$QF" -i expand_1/3" # 1)
QF=$QF" -i expand_2/4" # 1)
QF=$QF" -i lookup/2" # 1)
QF=$QF" -i lookup_all/2" # 1)
QF=$QF" -i is_defined/2" # 1)
QF=$QF" -i get_value/3" # 1)
QF=$QF" -i get_all_values/2" # 1)
QF=$QF" -i split/3" # 1)
QF=$QF" -i to_map/1" # 1)
../../ety --type-overlay overlay.erl --no-deps -f -l info stdlib/proplists2.erl $QF

../../ety --report-mode report --report-timeout 10000 --type-overlay overlay.erl --no-deps -f stdlib/proplists2.erl
