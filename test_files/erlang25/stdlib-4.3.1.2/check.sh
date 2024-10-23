#!/bin/bash

if [ -z "$1" ]; then
    opts="-P ."
fi

cd $(dirname $0)
../../../ety --build --no-type-checking -S src -I include/ -I ../kernel-8.5.4.1/include/ $opts "$@"
