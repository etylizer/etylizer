#!/bin/bash
set -e

cd $(dirname $0)

# added 11 missing type specs
# 1) redundant branch at top-level 
# 2) imprecise spec
# 3) exhaustiveness at top-level
# 4) overlay for lists:reverse to add the nonempty_list -> nonempty_list case
# 5) exhaustiveness
QF=""
QF=$QF" -i is_empty/1" # 1)
QF=$QF" -i len/1" # 1)
QF=$QF" -i to_list/1" # 1)
QF=$QF" -i from_list/1" # 1)
QF=$QF" -i member/2" # 1)
QF=$QF" -i in/2" # 1)
QF=$QF" -i in_r/2" # 1)
QF=$QF" -i get/2" # 2) 3)
QF=$QF" -i get_r/1" # 1)
QF=$QF" -i peek/1" # 1)
QF=$QF" -i peek_r/1" # 1)
QF=$QF" -i drop/1" # 4) 
QF=$QF" -i drop_r/1" # 4)
QF=$QF" -i reverse/1" # 1)
QF=$QF" -i join/2" # 1)
QF=$QF" -i split/2" # 5)
QF=$QF" -i split_f1_to_r2/5" # 3)
QF=$QF" -i split_r1_to_f2/5" # 3)
QF=$QF" -i delete/2" # 1)
QF=$QF" -i delete_r/2" # 1)
../../ety --type-overlay overlay_queue.erl --no-deps -l info -f stdlib/queue2.erl $QF

../../ety --report-mode report --report-timeout 1000 --type-overlay overlay_queue.erl --no-deps -f stdlib/queue2.erl
