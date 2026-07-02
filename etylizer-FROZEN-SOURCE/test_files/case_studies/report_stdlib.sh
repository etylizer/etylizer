#!/bin/bash

cd $(dirname $0)


../../ety --report-mode report --type-overlay overlay.erl --no-deps -f stdlib/orddict2.erl stdlib/proplists2.erl stdlib/queue2.erl stdlib/sets2.erl
