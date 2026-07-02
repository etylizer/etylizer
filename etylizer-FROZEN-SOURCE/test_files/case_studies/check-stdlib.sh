#!/bin/bash

cd $(dirname $0)

./check-proplists.sh
./check-ordsets.sh
./check-orddict.sh
./check-queue.sh
./check-sets.sh
