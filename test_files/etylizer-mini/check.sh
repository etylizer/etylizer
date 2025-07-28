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

# type error: 1
#   to_loc/2 (#238)
run_ety \
    --ignore to_loc/2 \
    src/ast.erl

run_ety src/ast_erl.erl

# type error:
#   mk_union/1 (90s) unknown
#   mk_intersection/1 (90s) unknown
# false positive: 2
#   unfold_intersection/2 unfold_union/2 (#241)
run_ety src/ast_lib.erl \
  -i unfold_intersection -i unfold_union \
  -i mk_union/1 \
  -i mk_intersection/1 

# slow:
#   resolve_ety_ty/3 (20s)
#
# try support: 1
#   eval_const_ty/2
#
# timeout:
#  trans_guards/3
#  trans_qualifier/3
#  trans_form/3
#  trans_spec_ty/3
#
# bug:
#  trans_ty/3 (TODO ty_parser)
#  trans_pat/4 (TODO ty_parser)
#  trans_pats/4 (TODO ty_parser)
#  trans_pat_bin_elem/4 (TODO ty_parser)
#
# new type error: 9
#  thread_through_env/3 unknown
#  shallow_remove_match/1 unknown
#  trans_exp/3 unknown
#  trans_catch_clause/3 unknown
#  trans_record_field/3 unknown
#  trans_if_clause/3 unknown
#  trans_fun_clause/3 unknown
#  trans/4 unknown
#  trans_constraint/3 unknown
#
# type error: 2
#  make_tyenv/3 (type error, empty var env is not compatible with tyenv()!)
#  build_funenv/2 unknown
run_ety src/ast_transform.erl \
    --ignore thread_through_env/3 \
    --ignore eval_const_ty/2 \
    --ignore shallow_remove_match/1 \
    --ignore trans_ty/3 \
    --ignore trans_guards/3 \
    --ignore trans_qualifier/3 \
    --ignore trans_exp/3 \
    --ignore trans_pat/4 \
    --ignore trans_pats/4 \
    --ignore trans_pat_bin_elem/4 \
    --ignore trans_catch_clause/3 \
    --ignore trans_record_field/3 \
    --ignore trans_if_clause/3 \
    --ignore trans_fun_clause/3 \
    --ignore trans/4 \
    --ignore trans_constraint/3 \
    --ignore make_tyenv/3 \
    --ignore trans_form/3 \
    --ignore trans_spec_ty/3 \
    --ignore build_funenv/2

# false positives: 2
#   referenced_modules/1 referenced_variables/1 (utils:everything)
run_ety \
    --ignore referenced_modules/1 \
    --ignore referenced_variables/1 \
    src/ast_utils.erl

run_ety src/errors.erl

# 5/12
# false positive: 2
#   macro_log/5 (#230)
#   parse_level/1 (#239)
# type error: 1
#   allow/1 (#12)
# receive and try supp: 5
#   get_logger_pid shutdown file_logger log_to_file
run_ety \
    --ignore allow/1 \
    --ignore macro_log/5 \
    --ignore parse_level/1 \
    --ignore get_logger_pid --ignore shutdown --ignore file_logger --ignore log_to_file \
    src/log.erl

# 3/5
# bug:
#   parse_file/2 (TODO ty_parser)
# try support: 1
#   parse_transform/2
run_ety \
    --ignore parse_file/2 \
    --ignore parse_transform/2 \
    src/parse.erl

# 4/5
# type error:
#   lookup_field_index/3
run_ety \
    --ignore lookup_field_index/3 \
    src/records.erl

# timeout:
#   tspecial_any/0
#   expand_predef_alias/1
#   builtin_ops/0
# false positive:
#   mk_builtin_funs/1 (#240)
# type error:
#   builtin_funs/0 (#12)
run_ety src/stdtypes.erl \
  --ignore expand_predef_alias/1 \
  --ignore tspecial_any/0 \
  --ignore mk_builtin_funs/1 \
  --ignore builtin_ops/0 \
  --ignore builtin_funs/0

# 3/5
# try support: 2
#   with_tmp_file with_tmp_dir
run_ety \
    --ignore with_tmp_file/4 --ignore with_tmp_dir/4 \
    src/tmp.erl

# timeout:
#   is_same_file/2
# bug:
#   hash_sha1 (TODO ty_parser)
#   hash_file (TODO ty_parser)
# type error: 5
#  diff_terms/3 io:format not compatible
#  unconsult/2, mkdirs/1: #12
#  quit/2 quit/3: spec wrong
# try support: 3
#  timeout/2 file_get_lines/1 sformat/2
# false positives: 2
#  everywhere/2 
#  everything/2
# type overlay: fl/1
run_ety --ignore fl/1 \
    --ignore is_same_file/2 \
    --ignore hash_sha1/1 \
    --ignore hash_file/1 \
    --ignore sformat/2 \
    --ignore everything/2 -i everywhere/2 -i diff_terms/3 --ignore file_get_lines/1 \
    --ignore mkdirs/1 \
    --ignore timeout/2 --ignore unconsult/2 -i quit/2 -i quit/3\
    src/utils.erl

# 6/6
run_ety src/varenv.erl

# 6/6
run_ety src/varenv_local.erl

# # 2/2
run_ety src/ast_erl.erl

# 0/0
run_ety src/t.erl
