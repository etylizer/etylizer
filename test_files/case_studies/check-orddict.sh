#!/bin/bash
set -e

cd $(dirname $0)

# 1) type spec error

QF=""
QF=$QF" -i append/3" # 1)
QF=$QF" -i append_list/3" # 1)
QF=$QF" -i update_counter/3" # 1)
QF=$QF" -i merge/3" # 1)
../../ety --type-overlay overlay.erl --no-deps -f -l info stdlib/orddict2.erl $QF

../../ety --report-mode report --report-timeout 13000 --type-overlay overlay.erl --no-deps -f stdlib/orddict2.erl
