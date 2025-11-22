#!/bin/bash
set -e

cd $(dirname $0)

# 1) exhaustiveness at top-level
# 2) redundant guard at top-level making things non-exhaustive
# 3) type spec wrong
# 4) overlay type needed
QF=""
QF=$QF" -i fetch/2" # 1)
QF=$QF" -i update/3" # 1)
QF=$QF" -i fold/3" # 1) or 2)
QF=$QF" -i map/2" # 1) or 2)
QF=$QF" -i filter/2" # 1) or 2)
QF=$QF" -i append/3" # 3)
QF=$QF" -i append_list/3" # 3)
QF=$QF" -i update_counter/3" # 3)
QF=$QF" -i from_list/1" # 4) requires overlay for lists:ukeysort/2
QF=$QF" -i merge/3" # 3)
../../ety --type-overlay overlay.erl --no-deps -f -l info stdlib/orddict2.erl $QF

../../ety --report-mode report --report-timeout 3000 --type-overlay overlay.erl --no-deps -f stdlib/orddict2.erl
