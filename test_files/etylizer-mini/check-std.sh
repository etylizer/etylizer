#!/bin/bash

cd $(dirname $0)

# type errors:
#  intersection/1 exhaustiveness needed
./ety --build --no-deps -f -l debug test_files/etylizer-mini/stdlib/ordsets2.erl -i intersection/1

# slow:
#  join/2 (25s)
#  filter_f/2 (75s)
# timeouts:
#  split/2
# type errors:
#  split_f1_to_r2
#  split_r1_to_f2
#  get/2
#  get_r/1 imprecise
#  peek/1 imprecise
#  peek_r/1 imprecise
#  out/1 unknown
#  out_r/1 unknown
#  drop/1 unknown
#  drop_r/1 unknown
#  delete_with/2 unknown
#  delete/2 unknown
#  delete_front unknown
#  r2f + operation
#  f2r + operation
./ety --build --no-deps -f -l debug test_files/etylizer-mini/stdlib/queue2.erl \
  -i out \
  -i out_r \
  -i get/2 \
  -i get_r \
  -i peek \
  -i peek_r \
  -i drop \
  -i drop_r \
  -i split \
  -i split_f1_to_r2 \
  -i split_r1_to_f2 \
  -i delete \
  -i delete_front \
  -i delete_with \
  -i r2f -i f2r 

