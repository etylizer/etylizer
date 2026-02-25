#!/bin/bash
set -e


TYPE_LIB="./src/"

ETY_FLAGS=(
    -P .
    --report-mode report
    --report-timeout 25000
    -I ./include
    -I ./src
    -I ./erlang_types
    -I ./erlang_types/dnf
    -l error
    --type-overlay overlays/etylizer_overlay.erl
    -f
    --no-deps
)

# make build > /dev/null

check() {
    local file="$1"
    shift
    ./ety "${ETY_FLAGS[@]}" "$@" "$TYPE_LIB""$file"
}

# ===== Fully clean files =====
check ast_lib.erl
check tally.erl
check t.erl
check subty.erl
check varenv.erl
check errors.erl
check ast_erl.erl
check constr.erl
check tyutils.erl
check records.erl
check log.erl
check tmp.erl
check ast.erl
check cm_depgraph.erl
check typing_common.erl
check paths.erl
check pretty.erl
check constr_error_locs.erl
check ast_utils.erl
check constr_collect.erl
check utils.erl
check graph.erl
check varenv_local.erl
check attr.erl
check cm_check.erl
check constr_simp.erl
check parse_cache.erl
check parse.erl
check typing_infer.erl
check symtab.erl
check constr_solve.erl
check gradual_utils.erl
check stdtypes.erl
check cm_index.erl
check typing.erl
check subst.erl
check etylizer_main.erl
check ast_check.erl
check typing_check.erl
check cm_module_interface.erl
check constr_gen.erl #-i exp_constrs/3 -i exp_constrs_2/3 -i exp_constrs_3/3 -i bin_expr_constrs/3 -i process_qualifiers/5 -i receive_clause_constrs/3 -i scrut_constrs_compact/3 -i case_clause_constrs/9 -i ty_of_pat/4 -i ty_of_bin_pat/2 -i pat_env/4 -i bin_elem_pat_env/3 -i guard_test_env/1 -i refine_eq_env/2 -i var_test_env/3 -i fun_clauses_to_exp_mixed/4 -i fun_clauses_to_exp_mixed_multi/4 -i fun_clauses_to_exp_aux/3 -i if_exp_to_case_exp/1

#check "$@"

# # ===== Files with ignored functions =====
# check ast_transform.erl -i trans/4 -i build_funenv/2 -i trans_form/3 -i trans_spec_ty/3 -i make_tyenv/3 -i trans_tydef/2 -i trans_constraint/3 -i eval_const_ty/2 -i eval_type_int/1 -i trans_ty/3 -i trans_ty_map_assoc/3 -i trans_guards/3 -i shallow_remove_match/1 -i trans_exp_seq/3 -i trans_exp/3 -i trans_maybe/4 -i trans_exp_bin_elem/3 -i resolve_name/5 -i trans_pat/4 -i trans_pat_bin_elem/4 -i trans_case_clauses/3 -i trans_case_clause/3 -i trans_catch_clause/3 -i trans_fun_clauses/4 -i trans_fun_clause/3 -i trans_if_clauses/3 -i trans_if_clause/3 -i trans_qualifier/3 -i trans_map_assoc/3 -i fill_record_defaults/4 -i trans_record_field/3 -i get_fresh_var_name/1 -i collect_record_variants/1 -i parse_type/2 -i is_error_clause/1 -i add_exhaustive_clause/2 -i optimize_dispatched_clauses/1 -i classify_positions/2 -i complex_has_catchall/2 -i pat_is_catchall/1 -i rewrite_dispatched_clauses/2 -i subst_local_refs/2 -i subst_local_refs_list/2 -i guards_ref_direct_vars/2 -i has_local_ref/2 -i has_local_ref_list/2 -i store_record_variant/2
