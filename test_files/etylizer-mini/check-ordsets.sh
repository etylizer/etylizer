#!/bin/bash
set -e

cd $(dirname $0)

# is_set/1 type error & crash
# added 2 missing type specs 
../../ety --no-deps -l info -f stdlib/ordsets2.erl -i is_set/1

../../ety --report-mode report --report-timeout 3000 --no-deps -f stdlib/ordsets2.erl
