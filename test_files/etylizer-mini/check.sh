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

run_ety src/varenv.erl
run_ety src/varenv_local.erl

# unconsult/2, mkdirs/1: #12
# hash_file/1: Name error: hash_sha1/1 undefined
# diff_terms/3: Name error: sformat/3 undefined
# fails type check:
#  is_same_file/2
#  mingle/5
#  sformat_raw/2
#  quit/2
# try support:
#  timeout/2 file_get_lines/1 sformat/2
# ignored because of missing support for binary:
#   sformat_raw/2, diff_terms/3, mkdirs/1
# hard:
#  everywhere/2 
#  everything/2
run_ety \
    --ignore is_same_file/2 --ignore quit/2 --ignore sformat_raw/2 --ignore sformat/2 \
    --ignore everything/2 --ignore everywhere/2 --ignore diff_terms/3 --ignore file_get_lines/1 \
    --ignore mkdirs/1 --ignore hash_file/1 \
    --ignore timeout/2 --ignore mingle/5 --ignore unconsult/2 \
    src/utils.erl

# with_tmp_file/4 and with_tmp_dir/4 because they use try
run_ety \
    --ignore with_tmp_file/4 --ignore with_tmp_dir/4 \
    src/tmp.erl

run_ety src/t.erl

run_ety src/errors.erl

# skip: too slow because of inference -> infer for single functions first, not everything at once
# run_ety src/stdtypes.erl

# trans_tys/3 timeout
# trans_ty_map_assoc/3 timeout
# shallow_remove_match/1 timeout
# trans/4 timeout
# trans_form/3 timeout
# trans_guards/3 timeout
# trans_exp/3 timeout
# trans_case_clause/3 timeout
# trans_case_clauses/3 timeout
# trans_catch_clause/3 timeout
# trans_catch_clauses/3 timeout
# trans_fun_clause/3 timeout
# trans_fun_clauses/3 timeout
# trans_if_clause/3 timeout
# trans_if_clauses/3 timeout
# trans_qualifier/3 timeout
# trans_qualifiers/3 timeout
# trans_pat/4 timeout
# trans_pats/4 timeout
# trans_pat_bin_elem/4 timeout
# trans_exps/3 timeout
# trans_exp_bin_elem/3 timeout
# trans_exp_noenv/3 timeout
# trans_exp_seq_noenv/3 timeout
# trans_exp_seq/3 timeout
# trans_map_assoc/3 timeout
# trans_map_assocs/3 timeout
# trans_record_field/3 timeout
# trans_record_fields/3 timeout
# trans_tydef/2 timeout
# trans_constraint/3 timeout
# resolve_ety_ty/3 timeout
# eval_const_ty/2 try support
# Slow:
#  thread_through_env/3
# Type error: 
#  trans_ty/3
#  build_funenv/2
#  trans_tydef/2
#  trans_spec_ty/3
#  make_tyenv/3
run_ety src/ast_transform.erl \
    --ignore thread_through_env/3 \
    --ignore eval_const_ty/2 \
    --ignore shallow_remove_match/1 \
    --ignore trans_ty/3 \
    --ignore trans_guards/3 \
    --ignore trans_ty_map_assoc/3 \
    --ignore trans_tys/3 \
    --ignore trans_qualifier/3 \
    --ignore trans_qualifiers/3 \
    --ignore trans_exp/3 \
    --ignore trans_exps/3 \
    --ignore trans_pat/4 \
    --ignore trans_pats/4 \
    --ignore trans_pat_bin_elem/4 \
    --ignore trans_catch_clause/3 \
    --ignore trans_catch_clauses/3 \
    --ignore trans_case_clause/3 \
    --ignore trans_case_clauses/3 \
    --ignore trans_record_field/3 \
    --ignore trans_record_fields/3 \
    --ignore trans_map_assoc/3 \
    --ignore trans_map_assocs/3 \
    --ignore trans_if_clause/3 \
    --ignore trans_if_clauses/3 \
    --ignore trans_fun_clause/3 \
    --ignore trans_fun_clauses/3 \
    --ignore trans_exp_noenv/3 \
    --ignore trans_exp_seq/3 \
    --ignore trans_exp_bin_elem/3 \
    --ignore trans_exp_seq_noenv/3 \
    --ignore trans/4 \
    --ignore resolve_ety_ty/3 \
    --ignore trans_constraint/3 \
    --ignore trans_tydef/2 \
    --ignore make_tyenv/3 \
    --ignore trans_form/3 \
    --ignore trans_spec_ty/3 \
    --ignore build_funenv/2

# to_loc/2 : type error
run_ety \
    --ignore to_loc/2 \
    src/ast.erl

run_ety src/ast_erl.erl

# record_ty_from_decl/2: timeout
# lookup_field_ty/3: timeout
# lookup_field_index/3: timeout
# encode_record_ty/2: timeout
run_ety \
    --ignore record_ty_from_decl/2 \
    --ignore encode_record_ty/2 \
    --ignore lookup_field_ty/3 \
    --ignore lookup_field_index/3 \
    src/records.erl

# timeout: parse_file/2 parse_file_or_die/2
# type error: parse_file_or_die/1
# try: parse_transform/2
run_ety \
    --ignore parse_file/2 \
    --ignore parse_file_or_die/2 \
    --ignore parse_file_or_die/1 \
    --ignore parse_transform/2 \
    src/parse.erl

# BUG: macro_log/5
# type error: allow/1 (#12)
# type error: parse_level/1
# get_logger_pid shutdown file_logger log_to_file: receive & try
run_ety \
    --ignore allow/1 \
    --ignore macro_log/5 \
    --ignore parse_level/1 \
    --ignore get_logger_pid --ignore shutdown --ignore file_logger --ignore log_to_file \
    src/log.erl

# type error: modname_from_path/1 referenced_modules/1 referenced_variables/1
# timeout: remove_locs/1
run_ety \
    --ignore modname_from_path/1 \
    --ignore referenced_modules/1 \
    --ignore referenced_variables/1 \
    --ignore remove_locs/1 \
    src/ast_utils.erl

# inference slow
# run_ety src/ast_erl.erl
