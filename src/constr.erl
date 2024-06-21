-module(constr).

% @doc This module defines types for constraints.

-export_type([
    locs/0,
    constr_env/0,
    constr_poly_env/0,
    constrs/0,
    constr/0,
    simp_constrs/0,
    simp_constr/0,
    constr_subty/0,
    constr_var/0,
    constr_def/0,
    constr_case_branch/0,
    case_branch_payload/0,
    constr_case_branch_cond/0,
    constrs_with_env/0
]).

-export([
    case_branch_guard/1,
    case_branch_body/1,
    case_branch_bodyCond/1,
    case_branch_result/1,
    mk_case_branch_payload/4
    ]).

-type locs() :: {string(), sets:set(ast:loc())}.
-type constr_env() :: #{ast:any_ref() => ast:ty()}.
-type constr_poly_env() :: #{ast:any_ref() => ast:ty_scheme()}.

% Constraints
-type constrs() :: sets:set(constr()).
-type constr() :: constr_subty() | constr_var() | constr_op() | constr_def()
                | constr_case() | constr_unsatisfiable().

-type simp_constrs() :: sets:set(simp_constr()).
-type simp_constr() :: constr_subty() | constr_unsatisfiable().

-type constr_subty() :: {csubty, locs(), ast:ty(), ast:ty()}.
-type constr_var() :: {cvar, locs(), ast:any_ref(), ast:ty()}.
-type constr_op() :: {cop, locs(), atom(), arity(), ast:ty()}.
-type constr_def() :: {cdef, locs(), constr_env(), constrs()}.
-type constr_unsatisfiable() :: {cunsatisfiable, ast:loc(), string()}.

% Cases
-type constr_case() :: {ccase,
                        locs(),
                        Scrutiny::constrs(),
                        Exhaustiveness::constrs(),
                        [constr_case_branch()]}.

-record(case_branch_payload, {
    % constraints for the guard of the branch
    guard :: constrs_with_env(),
    % constraints for the body of the branch (without the constraint for the result type)
    body :: constrs_with_env(),
    % constraints for ignoring the branch: if the constraints are satisifiable, the branch
    % can be ignored
    bodyCond :: constr_case_branch_cond(),
    % constraints for the result type (has same env as body)
    result :: constrs()
    }).
-type case_branch_payload() :: #case_branch_payload{}.

-spec mk_case_branch_payload(
    constrs_with_env(), constrs_with_env(), constr_case_branch_cond(), constrs()
) -> case_branch_payload.
mk_case_branch_payload(G, B, C, R) ->
    #case_branch_payload { guard = G, body = B, bodyCond = C, result = R}.

-spec case_branch_guard(case_branch_payload()) -> constrs_with_env().
case_branch_guard(X) -> X#case_branch_payload.guard.

-spec case_branch_body(case_branch_payload()) -> constrs_with_env().
case_branch_body(X) -> X#case_branch_payload.body.

-spec case_branch_bodyCond(case_branch_payload()) -> constrs_with_env().
case_branch_bodyCond(X) -> X#case_branch_payload.bodyCond.

-spec case_branch_result(case_branch_payload()) -> constrs_with_env().
case_branch_result(X) -> X#case_branch_payload.result.

-type constr_case_branch_cond() :: none | constrs().
-type constr_case_branch() ::
        {ccase_branch, locs(), case_branch_payload()}. % with ccase_body
-type constrs_with_env() :: {constr_env(), constrs()}.
