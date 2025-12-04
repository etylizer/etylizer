#!/bin/bash

cd $(dirname $0)
OVERLAY=overlay.erl
LOGLEVEL=info

if [ ! -z "$ETYLIZER_CASE_STUDY_LOGLEVEL" ]; then
    LOGLEVEL="$ETYLIZER_CASE_STUDY_LOGLEVEL"
fi

function run_ety() {
    ../../ety --build --type-overlay $OVERLAY --force -l $LOGLEVEL -P . -I src $QF --no-deps "$@" || exit 1
}

# to) timeout
# 1) impl: try & catch
# 2) rank-2 types needed: Scrap your boilerplate PLDI'03
# 3) design: exhaustiveness with A = B #12
# 4) impl: nominal types not supported
# 5) possible (passes type check), but needs a term() -> fun_types() function to verify the data returned 
#    by the ets call or when types are lost with nested higher order functions

QF=""
QF=$QF" -i to_loc/2" # 4)
run_ety src/ast.erl

QF=""
run_ety src/ast_erl.erl

QF=""
run_ety src/ast_lib.erl

QF=""
QF=" -i remove_locs/1" # 2)
run_ety src/ast_utils.erl

QF=""
run_ety src/errors.erl

QF=""
QF=$QF" -i allow/1" # 3)
QF=$QF" -i get_logger_pid" # 1)
QF=$QF" -i shutdown" # 1)
QF=$QF" -i file_logger" # 1)
QF=$QF" -i log_to_file" # 1)
run_ety src/log.erl

QF=""
QF=$QF" -i parse_file/2" # 4)
QF=$QF" -i parse_transform/2" # 3)
run_ety src/parse.erl

QF="" run_ety src/records.erl

QF=""
QF=$QF" -i expand_predef_alias/1" # to)
QF=$QF" -i builtin_ops/0" # to)
QF=$QF" -i mk_builtin_funs/1" # 5) 
QF=$QF" -i builtin_funs/0" # 5)
run_ety src/stdtypes.erl

QF=""
QF=$QF" -i with_tmp_file/4" # 1)
QF=$QF" -i with_tmp_dir/4" # 1)
run_ety src/tmp.erl

QF="" run_ety src/varenv.erl

QF="" run_ety src/varenv_local.erl

QF="" run_ety src/ast_erl.erl

QF="" run_ety src/t.erl

QF="" 
QF=$QF" -i is_same_file/2" # to) unoptimized andalso chaining
QF=$QF" -i unconsult/2" # 3)
QF=$QF" -i mkdirs/1" # 3)
QF=$QF" -i timeout/2" # 1)
QF=$QF" -i file_get_lines/1" # 1)
QF=$QF" -i sformat/2" # 1)
QF=$QF" -i fl/1" # not part of case study (overlay with additional -type)
run_ety src/utils.erl

QF="" 
QF=$QF" -i resolve_ety_ty/3" # 80s
QF=$QF" -i eval_const_ty/2" # 1)
QF=$QF" -i shallow_remove_match/1" # to)
QF=$QF" -i trans_guards/3" # to)
QF=$QF" -i trans_qualifier/3" # to)
QF=$QF" -i trans_form/3" # to)
QF=$QF" -i trans_spec_ty/3" # to)
QF=$QF" -i trans_ty/3" # 4)
QF=$QF" -i trans_pat/4" # 4)
QF=$QF" -i trans_exp/3" # to)
QF=$QF" -i trans/4" # to) tally v1 is faster check why
QF=$QF" -i trans_catch_clause/3" # 3)
QF=$QF" -i build_funenv/2" # 5) implemented assert fun
QF=$QF" -i mk_builtin_funs/2" # 5) implemented assert fun
QF=$QF" -i assert_funs/1" # 5) type overlap
run_ety src/ast_transform.erl
