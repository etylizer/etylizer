#!/bin/bash

cd $(dirname $0)

# stdlib
../../ety --build -l error --report-mode report --no-deps -f --report-timeout 5000 --type-overlay overlay.erl stdlib/maps2.erl
#../../ety --build -l error --report-mode report --no-deps -f --report-timeout 5000 --type-overlay overlay.erl stdlib/orddict2.erl
