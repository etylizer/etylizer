#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl
LOGLEVEL=debug

if [ ! -z "$ETYLIZER_CASE_STUDY_LOGLEVEL" ]; then
    LOGLEVEL="$ETYLIZER_CASE_STUDY_LOGLEVEL"
fi

function run_ety() {
    ../../ety --build --type-overlay $OVERLAY --force --level $LOGLEVEL -P . -I src --no-deps "$@" || exit 1
}

# 9/10
# type error: 1
#   to_loc/2 (#238)
run_ety \
    --ignore to_loc/2 \
    src/ast.erl

# 2/2
run_ety src/ast_erl.erl

# 1/8
# false positive: 2
#   unfold_intersection/2 unfold_union/2 (#241)
# timeout: 5
run_ety src/ast_lib.erl \
  -i unfold_intersection -i unfold_union \
  -i mk_intersection/2 -i mk_intersection/1 -i mk_diff \
  -i mk_union/1 -i mk_union/2

# 6/43
# timeout: 32
# try support: 1
#   eval_const_ty/2
# type error: 4
#  make_tyenv/3 (type error, empty var env is not compatible with tyenv()!)
#  trans_ty/3 (error log format!) 
#  build_funenv/2 (???)
#  trans_tydef/2 (???)
# false positive: 1
#  trans_spec_ty/3 (utils:everything)
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

# 2/4
# false positives: 2
#   referenced_modules/1 referenced_variables/1 (utils:everything)
run_ety \
    --ignore referenced_modules/1 \
    --ignore referenced_variables/1 \
    src/ast_utils.erl

# 17/17
run_ety src/errors.erl

# 5/12
# false positive: 2
#   macro_log/5 (#230)
#   parse_level/1 (#239)
# type error: 1
#   allow/1 (#12)
# receive and try supp: 5
#   get_logger_pid shutdown file_logger log_to_file
run_ety -o get_logl_level/1 \
    --ignore allow/1 \
    --ignore macro_log/5 \
    --ignore parse_level/1 \
    --ignore get_logger_pid --ignore shutdown --ignore file_logger --ignore log_to_file \
    src/log.erl

# 2/5
# timeout: 2
# try support: 1
#   parse_transform/2
run_ety \
    --ignore parse_file/2 \
    --ignore parse_file_or_die/2 \
    --ignore parse_transform/2 \
    src/parse.erl

# 1/5
# timeout: 4
run_ety \
    --ignore record_ty_from_decl/2 \
    --ignore encode_record_ty/2 \
    --ignore lookup_field_ty/3 \
    --ignore lookup_field_index/3 \
    src/records.erl

# 29/55 in 67s
# false positive: 1
#   mk_builtin_funs/1 (#240)
# type error: 1
#   builtin_funs/0 (#12)
# timeout: 24
run_ety src/stdtypes.erl \
  --ignore extra_funs/0 \
  --ignore tmu/2 \
  --ignore tinter/1 \
  --ignore tinter/2 \
  --ignore tfun/2 \
  --ignore tfun1/2 \
  --ignore tfun2/3 \
  --ignore tatom/0 \
  --ignore tmap/1 \
  --ignore tmap/2 \
  --ignore tmap_req/2 \
  --ignore tmap_field_opt/2 \
  --ignore tmap_field_req/2 \
  --ignore tfun_full/2 \
  --ignore ttuple/1 \
  --ignore ttuple1/1 \
  --ignore ttuple2/2 \
  --ignore tintersect/1 \
  --ignore tunion/1 \
  --ignore tunion/2 \
  --ignore tspecial_any/0 \
  --ignore expand_predef_alias/1 \
  --ignore tyscm/1 \
  --ignore tyscm/2 \
  --ignore builtin_ops/0 \
  --ignore mk_builtin_funs/1 \
  --ignore builtin_funs/0

# 3/5
# try support: 2
#   with_tmp_file with_tmp_dir
run_ety \
    --ignore with_tmp_file/4 --ignore with_tmp_dir/4 \
    src/tmp.erl

# 39/49
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
