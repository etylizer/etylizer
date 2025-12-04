#!/bin/bash
set -e

cd $(dirname $0)

# is_set/1 type error & crash
# filtermap/2 type error
# added 2 missing type specs 
../../ety --no-deps -l info -f stdlib/ordsets2.erl -i is_set/1 -i filtermap/2

../../ety --report-mode report --report-timeout 10000 --no-deps -f stdlib/ordsets2.erl
