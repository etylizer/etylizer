#!/bin/bash

cd $(dirname $0)

../../ety --build --no-deps -f -l debug stdlib/ordsets2.erl -i intersection/1

# drop_r drop out out_r memory exhaustive
# delete_with/2 split/2 delete/2 timeout
# delete_front unknown type error
# f2r/1 r2f/1 get/2 get_r/1 peek/1 peek_r/1 type error, imprecise
# split_f1_to_r2 split_r1_to_f2 exhaustiveness fail
# filter_f filtermap_r needs function optimizations
../../ety --build --no-deps -f -l debug stdlib/queue2.erl \
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
  -i r2f -i f2r \
  -i filter_f \
  -i filtermap_r

