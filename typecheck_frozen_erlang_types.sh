#!/bin/bash
set -e

# Run from the parent etylizer project. Uses THIS project's etylizer
# (./ety --build, the current build) to typecheck the FROZEN source's
# src/erlang_types library. All project/include/overlay/source paths below
# point into the frozen tree so the code under check is the frozen one.
FROZEN="./etylizer-FROZEN-SOURCE"

./ety --build -P "$FROZEN" \
    -I "$FROZEN/include" -I "$FROZEN/src" -I "$FROZEN/src/erlang_types" -I "$FROZEN/src/erlang_types/dnf" \
    --report-mode report --report-timeout 30000 \
    --type-overlay "$FROZEN/overlays/etylizer_overlay.erl" -f --no-deps -S "$FROZEN/src/erlang_types" \
    -i ast_transform -i constr_gen \
    -i count_features \
    -i utils:replace_term/2 \
    -i tally:eliminate_hubs/3 \
    -i ast_check:check_ty_type_simple2/3 \
    -i ast_check:check_ty_union/5 \
    -i typing_check:extract_loc/2 \
    -i pretty:render_exp/2 \
    -i pretty:render_clause/2 \
    -i pretty:render_fun_clause/2 \
    -i 'dnf_ty_predefined:is_empty/2' \
    -i 'dnf_ty_predefined:unparse/2' \
    "$@"
