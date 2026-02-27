#!/bin/bash
set -e
TYPE_LIB="./src/erlang_types/"

./ety --build -P . -I include -I src -I src/erlang_types -I src/erlang_types/dnf \
    --type-overlay overlays/etylizer_overlay.erl -f --no-deps -S src/erlang_types -S src \
    -i ast_transform -i constr_gen \
    -i constr_solve:check_simp_constrs/4 \
    -o ast_check:check_ty_remote/5 \
    -i count_features \
    -i utils:replace_term/2 \
    -i tally:eliminate_hubs/3 \
    -i ast_check:check_ty_type_simple2/3 \
    -i ast_check:check_ty_union/5 \
    -i typing_check:extract_loc/2 \
    -i pretty:render_exp/2 \
    -i pretty:render_clause/2 \
    -i pretty:render_fun_clause/2 \
    "$@"
