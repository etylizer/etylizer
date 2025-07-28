#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl
LOGLEVEL=debug

if [ ! -z "$ETYLIZER_CASE_STUDY_LOGLEVEL" ]; then
    LOGLEVEL="$ETYLIZER_CASE_STUDY_LOGLEVEL"
fi

function run_ety() {
    ../../ety --build --type-overlay $OVERLAY --force -l $LOGLEVEL -P . -I src --no-deps "$@" || exit 1
}

run_ety src/ast_neg.erl 
