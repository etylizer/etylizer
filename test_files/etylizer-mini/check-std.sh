#!/bin/bash

cd $(dirname $0)

../../ety --build --no-deps -f -l debug stdlib/ordsets2.erl -i intersection/1

# timeouts:
#  split/2
# type errors:
#  get_r/1 imprecise
#  peek/1 imprecise
#  peek_r/1 imprecise
#  filter_r/2
#  delete_with_front/2
#  delete_with_rear/2
#  out/1
#  out_r/1
#  drop/1
#  drop_r/1
#  delete_with/2
#  delete/2
#  filter_f
#  filtermap_r
#  delete_front
#  r2f
#  f2r
../../ety --build --no-deps -f -l debug stdlib/queue2.erl \
  -i filter_r/2 \
  -i delete_with_front/2 \
  -i delete_with_rear/2 \
  -i out \
  -i out_r \
  -i get_r \
  -i peek \
  -i peek_r \
  -i drop \
  -i drop_r \
  -i split \
  -i delete_with \
  -i delete \
  -i delete_front \
  -i r2f -i f2r \
  -i filter_f \
  -i filtermap_r

