#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl
LOGLEVEL=note

if [ ! -z "$ETYLIZER_CASE_STUDY_LOGLEVEL" ]; then
    LOGLEVEL="$ETYLIZER_CASE_STUDY_LOGLEVEL"
fi

function run_ety() {
    ../../ety --build --type-overlay $OVERLAY --force -l $LOGLEVEL -P . -I src $QF --no-deps "$@" || exit 1
}

# ?) TODO
# to) timeout
# fp) false positive
# p) positive
# 1) false positive
# 2) impl: try & catch
# 3) design: exhaustiveness with A = B #12
# 4) impl: strings as fine-grained lists
# 5) impl: nominal types not parsed and added
# 6) possible, but need custom guards to refine case branches

QF=""
QF=$QF" -i to_loc/2" # p) bad spec (#238)
run_ety src/ast.erl

QF=""
run_ety src/ast_erl.erl

QF=""
QF=$QF" -i mk_union/1" # p) branch can't happen
QF=$QF" -i mk_intersection" # p) branch can't hapen
run_ety src/ast_lib.erl

QF=""
run_ety src/ast_utils.erl

QF=""
run_ety src/errors.erl

QF=""
QF=$QF" -i allow/1" # 3)
QF=$QF" -i parse_level/1" # 4) #239
QF=$QF" -i get_logger_pid" # 2)
QF=$QF" -i shutdown" # 2)
QF=$QF" -i file_logger" # 2)
QF=$QF" -i log_to_file" # 2)
run_ety src/log.erl

QF=""
QF=$QF" -i parse_file/2" # 5)
QF=$QF" -i parse_transform/2" # 3)
run_ety src/parse.erl

# 1 positive: 
#  either we add 'untyped' to -type record_field() and encore_record_ty becomes a problem
#  or has a redundant branch
QF=""
QF=$QF" -i lookup_field_index/3" # p)
run_ety src/records.erl

QF=""
QF=$QF" -i expand_predef_alias/1" # to)
QF=$QF" -i builtin_ops/0" # to)
QF=$QF" -i mk_builtin_funs/1" # 6) 
QF=$QF" -i builtin_funs/0" # 6)
run_ety src/stdtypes.erl

QF=""
QF=$QF" -i with_tmp_file/4" # 2)
QF=$QF" -i with_tmp_dir/4" # 2)
run_ety src/tmp.erl

QF="" run_ety src/varenv.erl

QF="" 
QF=$QF" -i merge_envs/1" # ?) regression
run_ety src/varenv_local.erl

run_ety src/ast_erl.erl

run_ety src/t.erl

QF="" 
QF=$QF" -i is_same_file/2" # to) unoptimized andalso chaining
QF=$QF" -i hash_sha1" # ?) parser bug
QF=$QF" -i hash_file" # ?) parser bug
QF=$QF" -i diff_terms/3" # ?) name error, fun undefined
QF=$QF" -i unconsult/2" # 3)
QF=$QF" -i mkdirs/1" # 3)
QF=$QF" -i quit/2" # p)
QF=$QF" -i quit/3" # p)
QF=$QF" -i timeout/2" # 2)
QF=$QF" -i file_get_lines/1" # 2)
QF=$QF" -i sformat/2" # 2)
QF=$QF" -i everywhere/2" # ?) bug
QF=$QF" -i everything/2" # ?) bug
QF=$QF" -i fl/1" # ?) bug
QF=$QF" -i assocs_find_index/2" # ?) regression
run_ety src/utils.erl

QF="" 
QF=$QF" -i resolve_ety_ty/3" # 80s
QF=$QF" -i eval_const_ty/2" # 2)
QF=$QF" -i trans_guards/3" # to)
QF=$QF" -i trans_qualifier/3" # to)
QF=$QF" -i trans_form/3" # to)
QF=$QF" -i trans_spec_ty/3" # to)
QF=$QF" -i trans_ty/3" # ?) parser bug
QF=$QF" -i trans_pat/4" # ?) parser bug
QF=$QF" -i trans_exp/3" # to)
QF=$QF" -i trans_catch_clause/3" # 3)
QF=$QF" -i trans/4" # ?)
QF=$QF" -i make_tyenv/3" # p) empty var env is not compatible with tyenv()
QF=$QF" -i build_funenv/2" # fp) branch never matches fp
QF=$QF" -i shallow_remove_match/1" # ?) regression
run_ety src/ast_transform.erl
