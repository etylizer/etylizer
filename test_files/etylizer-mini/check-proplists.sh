#!/bin/bash

cd $(dirname $0)

# 1) comprehensions (fixed by PR #262)
# 2) difficult type spec TODO
# 3) requires tuple size refinement ('tuples larger-equal than 1')

QF=""
QF=$QF" -i compact/1" # 1)
QF=$QF" -i substitute_aliases/2" # 1)
QF=$QF" -i substitute_negations/2" # 1)
QF=$QF" -i split/2" # 1)
QF=$QF" -i expand/2" # 1) + 2)
QF=$QF" -i normalize/2" # 2)
QF=$QF" -i to_map/2" # 3)
QF=$QF" -i lookup/2" # 3)
QF=$QF" -i lookup_all/2" # 3)
QF=$QF" -i is_defined/2" # 3)
QF=$QF" -i get_all_value/2" # 3)
QF=$QF" -i append_values/2" # 3)
QF=$QF" -i get_bool/2" # 3)
QF=$QF" -i get_keys/2" # 3)
QF=$QF" -i delete/2" # 3)
QF=$QF" -i substitute_aliases_1/2" # 3)
QF=$QF" -i substitute_negations_1/2" # 3)
QF=$QF" -i expand_1/3" # 3)
QF=$QF" -i expand_2/4" # 3)
QF=$QF" -i lookup/2" # 3)
QF=$QF" -i lookup_all/2" # 3)
QF=$QF" -i is_defined/2" # 3)
QF=$QF" -i get_value/3" # 3)
QF=$QF" -i get_all_values/2" # 3)
QF=$QF" -i split/3" # 3)
QF=$QF" -i to_map/1" # 3)
../../ety --build --type-overlay overlay.erl --no-deps -f -l debug stdlib/proplists2.erl $QF
