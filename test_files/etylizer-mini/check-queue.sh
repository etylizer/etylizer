#!/bin/bash
set -e

cd $(dirname $0)

# added 11 missing type specs
# 1) transitive type error
# 2) imprecise spec
# 3) exhaustiveness disabled inside body
QF=""
QF=$QF" -i get/2" # 2)
QF=$QF" -i get/1" # 1) get/2
QF=$QF" -i head/1" # 1) get/2
../../ety --type-overlay overlay_queue.erl --no-deps -l info -f stdlib/queue2.erl $QF

../../ety --report-mode report --report-timeout 150000 --type-overlay overlay_queue.erl --no-deps -f stdlib/queue2.erl
