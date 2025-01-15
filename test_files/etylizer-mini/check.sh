#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl

# range excluded because it's slow, see #161
../../ety --build --force --level debug -P . -I src --no-deps --ignore range/1 src/varenv.erl

# merge_envs excluded because it's slow, see #161
../../ety --build --force --level debug -P . -I src --no-deps --ignore merge_envs/1 src/varenv_local.erl

# map_opt/3 ignored because it's not type correct
# ignored because of missing support for binary:
#   mingle/5, is_same_file/2, quit/3, quit/2, sformat_raw/2, diff_terms/3, mkdirs/1, hash_sha1/1,
#   hash_file/1, unconsult/2, file_exists/1
# sformat/2 and file_get_lines/1 and timeout/2 require support for try
# everywhere/2 and everything/2 because they are very hard to type check
# assocs_find_index/2 because recursive functions are slow to type check
../../ety --build --type-overlay $OVERLAY --force --level debug -P . -I src --no-deps \
    --ignore map_opt/3 --ignore quit/3 --ignore quit/2 --ignore sformat_raw/2 --ignore sformat/2 \
    --ignore everything/2 --ignore everywhere/2 --ignore diff_terms/3 --ignore file_get_lines/1 \
    --ignore mkdirs/1 --ignore hash_sha1/1 --ignore hash_file/1 --ignore assocs_find_index/2 \
    --ignore timeout/2 --ignore mingle/5 --ignore is_same_file/2 --ignore unconsult/2 \
    --ignore file_exists/1 \
    --ignore with_index/2 --ignore assocs_find/2 \
    src/utils.erl

# with_tmp_file/4 and with_tmp_dir/4 because they use try
# INVESTIGATE: tmp_dir/0
../../ety --build --type-overlay $OVERLAY --force --level debug -P . -I src --no-deps \
    --ignore tmp_dir/0 --ignore with_tmp_file/4 --ignore with_tmp_dir/4 \
    src/tmp.erl

../../ety --build --force --level debug -P . -I src --no-deps src/t.erl
../../ety --build --force --level debug -P . -I src --no-deps src/errors.erl

# skip: too slow because of inference
# ../../ety --build --force --level debug -P . -I src --no-deps src/stdtypes.erl

# Does not work because of #182
# ../../ety --build --force --level debug -P . -I src --no-deps src/ast_transform.erl

# missing support for binary: to_loc/2
# get_name_fun/1: #196
# loc_exp/1: too slow (needs overlay for element)
../../ety --build --type-overlay $OVERLAY --force --level debug -P . -I src --no-deps \
    --ignore to_loc/2 \
    --ignore get_fun_name/1 \
    --ignore loc_exp/1 \
    src/ast.erl

# FULL
# ../../ety --build --force --level debug -P . -I src "$@"
