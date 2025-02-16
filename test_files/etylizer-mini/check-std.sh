#!/bin/bash

cd $(dirname $0)

../../ety --build --no-deps -f -l info stdlib/ordsets2.erl

# drop_r drop out out_r memory exhaustive
# delete_with/2 split/2 delete/2 timeout
# delete_front unknown type error
# f2r/1 r2f/1 get/2 get_r/1 peek/1 peek_r/1 type error, imprecise
# split_f1_to_r2 split_r1_to_f2 exhaustiveness fail
../../ety --build --no-deps -f -l info stdlib/queue2.erl \
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

