#!/bin/bash

cd $(dirname $0)
#../../ety --build -P . -S src -I src "$@"
../../ety --build --force -P . -I src "$@"
