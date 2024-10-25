#!/bin/bash

cd $(dirname $0)
../../ety --build --no-type-checking -P . \
   -S kernel-8.5.4.1/src/  -I kernel-8.5.4.1/include/ \
   -S erts-13.2.2.2/src \
   -S stdlib-4.3.1.2/src -I stdlib-4.3.1.2/include \
   "$@"
