#!/bin/bash

cd $(dirname $0)

# range excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore range/1 src/varenv.erl

# merge_envs excluded because it's slow, see #161
# ../../ety --build --force --level debug -P . -I src --no-deps --ignore merge_envs/1 src/varenv_local.erl

../../ety --build --force --level debug -P . -I src --no-deps src/utils.erl

# FULL
# ../../ety --build --force --level debug -P . -I src "$@"
