#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl
LOGLEVEL=debug

if [ ! -z "$ETY_CASE_STUDY_LOGLEVEL" ]; then
    LOGLEVEL="$ETY_CASE_STUDY_LOGLEVEL"
fi

function run_ety() {
    ../../ety --build --type-overlay $OVERLAY --force --level $LOGLEVEL -P . -I src --no-deps "$@" || exit 1
}

# range/1 excluded because it's slow, see #161
# insert/4 and insert_if_absent/3 excluded, see #201
# find/2: raw_printing_bug #202
run_ety --ignore range/1 --ignore insert/4 --ignore insert_if_absent/3 --ignore find/2 src/varenv.erl

# merge_envs excluded because it's slow, see #161
# insert/2 and find/2 excluded, see #202
run_ety --ignore merge_envs/1 --ignore insert/2 --ignore find/2 src/varenv_local.erl

# ignored because of missing support for binary:
#   mingle/5, is_same_file/2, quit/3, quit/2, sformat_raw/2, diff_terms/3, mkdirs/1, hash_sha1/1,
#   hash_file/1, unconsult/2, file_exists/1
# sformat/2 and file_get_lines/1 and timeout/2 require support for try
# everywhere/2 and everything/2 because they are very hard to type check
# assocs_find_index/2 because recursive functions are slow to type check #163
run_ety \
    --ignore quit/3 --ignore quit/2 --ignore sformat_raw/2 --ignore sformat/2 \
    --ignore everything/2 --ignore everywhere/2 --ignore diff_terms/3 --ignore file_get_lines/1 \
    --ignore mkdirs/1 --ignore hash_sha1/1 --ignore hash_file/1 --ignore assocs_find_index/2 \
    --ignore timeout/2 --ignore mingle/5 --ignore is_same_file/2 --ignore unconsult/2 \
    --ignore file_exists/1 \
    --ignore assocs_find/2 \
    src/utils.erl

# with_tmp_file/4 and with_tmp_dir/4 because they use try
run_ety \
    --ignore with_tmp_file/4 --ignore with_tmp_dir/4 \
    src/tmp.erl

run_ety src/t.erl
run_ety src/errors.erl

# skip: too slow because of inference
# run_ety src/stdtypes.erl

# Too slow, probably because of recursive definitions #163
# run_ety src/ast_transform.erl

# missing support for binary: to_loc/2
# get_name_fun/1: too slow #196
# loc_exp/1: too slow (loc_exp/1 also needs overlay for erlang:element/2) #196
# format_loc/1: crashes with "no more index entries in atom_tab (max=1048576)" #196
run_ety \
    --ignore to_loc/2 \
    --ignore get_fun_name/1 \
    --ignore loc_exp/1 \
    --ignore format_loc/1 \
    src/ast.erl

# record_ty_from_decl/2: slow, maybe #196
# encode_record_ty/1 and lookup_field_ty/3: slow (very simple functions, maybe they are slow
#   because they uses the large type ast:ty()?) Could also be #196
# encode_record_ty/2: slow, maybe #196
run_ety \
    --ignore record_ty_from_decl/2 \
    --ignore encode_record_ty/1 \
    --ignore encode_record_ty/2 \
    --ignore lookup_field_ty/3 \
    --ignore lookup_field_index/3 \
    src/records.erl

# MISSING: src/parse.erl src/log.erl src/ast_utils.erl src/ast_lib.erl src/ast_erl.erl
