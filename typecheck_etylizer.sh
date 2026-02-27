#!/bin/bash
set -e

./ety --build -P . -I include -I src -I src/erlang_types -I src/erlang_types/dnf \
    --type-overlay overlays/etylizer_overlay.erl -S src/erlang_types -S src \
    -i ast_transform -i constr_gen \
    -i count_features \
    -i tally:eliminate_hubs/3 \
    -i ast_check:check_ty_type_simple2/3 \
    -i ast_check:check_ty_union/5 \
    -i typing_check:extract_loc/2 \
    -i pretty:render_exp/2 \
    -i pretty:render_clause/2 \
    -i pretty:render_fun_clause/2 \
    -i pretty:render_if_clause/2 \
    -i pretty:render_catch_clause/2 \
    -i pretty:render_qualifier/2 \
    "$@"
