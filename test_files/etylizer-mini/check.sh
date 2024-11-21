#!/bin/bash

cd $(dirname $0)

../../ety --build --force --level debug -P . -I src --no-deps src/varenv.erl

# FULL
# ../../ety --build --force --level debug -P . -I src "$@"
