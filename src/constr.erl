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
    constr_case_body/0
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
-type constr_case() :: {ccase,
                        locs(),
                        Scrutiny::constrs(),
                        [constr_case_body()]}.
-type constr_case_body_cond() :: none | constrs().
-type constr_case_body() ::
        {ccase_body, locs(), Guard::constrs_with_env(), Body::constrs_with_env(),
            BodyCond::constr_case_body_cond()}.
-type constrs_with_env() :: {constr_env(), constrs()}.
-type constr_unsatisfiable() :: {cunsatisfiable, ast:loc(), string()}.
