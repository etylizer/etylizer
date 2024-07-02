-module(constr).

% @doc This module defines types for constraints.

-export_type([
    locs/0,
    constr_env/0,
    constr_poly_env/0,
    constrs/0,
    constr/0,
    constr_subty/0,
    constr_var/0,
    constr_def/0,
    constr_case_branch/0,
    case_branch_payload/0,
    constr_case_branch_cond/0,
    constrs_with_env/0,
    simp_constrs/0,
    simp_constr/0,
    simp_constrs_loc/0,
    simp_constr_subty/0,
    simp_constr_case/0,
    simp_constr_case_branch/0,
    subty_constrs/0
]).

-export([
    case_branch_guard/1,
    case_branch_body/1,
    case_branch_bodyCond/1,
    case_branch_result/1,
    mk_case_branch_payload/4,
    locs_of_constr/1
    ]).

-type locs() :: {string(), sets:set(ast:loc())}.
-type constr_env() :: #{ast:any_ref() => ast:ty()}.
-type constr_poly_env() :: #{ast:any_ref() => ast:ty_scheme()}.

% Constraints
-type constrs() :: sets:set(constr()).
-type constr() :: constr_subty() | constr_var() | constr_op() | constr_def()
                | constr_case().

-type simp_constrs() :: sets:set(simp_constr()).
-type simp_constrs_loc() :: {ast:loc(), simp_constrs()}.
-type simp_constr() :: simp_constr_subty() | simp_constr_case().
-type subty_constrs() :: set:set(constr:simp_constr_subty()).

-type simp_constr_subty() :: {scsubty, ast:loc(), ast:ty(), ast:ty()}.
-type simp_constr_case() ::
    {sccase, Scrutiny::simp_constrs_loc(), Exhaustiveness::simp_constrs_loc(),
        [simp_constr_case_branch()]}.

-type simp_constr_case_branch() ::
    {sccase_branch, Guards::simp_constrs_loc(), Cond::simp_constrs_loc() | none,
        Body::simp_constrs_loc()}.

-type constr_subty() :: {csubty, locs(), ast:ty(), ast:ty()}.
-type constr_var() :: {cvar, locs(), ast:any_ref(), ast:ty()}.
-type constr_op() :: {cop, locs(), atom(), arity(), ast:ty()}.
-type constr_def() :: {cdef, locs(), constr_env(), constrs()}.

-spec locs_of_constr(constr()) -> locs().
locs_of_constr(C) ->
    case C of
        {csubty, Locs, _, _} -> Locs;
        {cvar, Locs, _, _} -> Locs;
        {cop, Locs, _, _, _} -> Locs;
        {cdef, Locs, _, _} -> Locs;
        {ccase, Locs, _, _, _} -> Locs
    end.

% Cases
-type constr_case() :: {ccase,
                        locs(),
                        Scrutiny::constrs(),
                        Exhaustiveness::constrs(),
                        [constr_case_branch()]}.

-type case_branch_payload() :: {
    % constraints for the guard of the branch
    Guard :: constrs_with_env(),
    % constraints for the body of the branch (without the constraint for the result type)
    Body :: constrs_with_env(),
    % constraints for ignoring the branch: if the constraints are satisifiable, the branch
    % can be ignored
    BodyCond :: constr_case_branch_cond(),
    % constraints for the result type (has same env as body)
    Result :: constrs()
    }.

-spec mk_case_branch_payload(
    constrs_with_env(), constrs_with_env(), constr_case_branch_cond(), constrs()
) -> case_branch_payload().
mk_case_branch_payload(G, B, C, R) -> {G, B, C, R}.

-spec case_branch_guard(case_branch_payload()) -> constrs_with_env().
case_branch_guard({G, _, _, _}) -> G.

-spec case_branch_body(case_branch_payload()) -> constrs_with_env().
case_branch_body({_, B, _, _}) -> B.

-spec case_branch_bodyCond(case_branch_payload()) -> constr_case_branch_cond().
case_branch_bodyCond({_, _, C, _}) -> C.

-spec case_branch_result(case_branch_payload()) -> constrs().
case_branch_result({_, _, _, R}) -> R.

-type constr_case_branch_cond() :: none | constrs().
-type constr_case_branch() ::
        {ccase_branch, locs(), case_branch_payload()}. % with ccase_body
-type constrs_with_env() :: {constr_env(), constrs()}.
