#!/bin/bash

cd $(dirname $0)

# ../../ety --build --no-deps -f -l debug stdlib/ordsets2.erl -i intersection/1

../../ety --build --no-deps -f -l debug stdlib/queue2.erl -o in/2
# -i in/2 -i join/2 -i filter/2 -i filtermap/2 -i fold/3 -i any/2 -i all/2 \
