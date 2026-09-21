-module(dead_code).

-compile(export_all).
-compile(nowarn_export_all).

% Expressions that can never be evaluated because a subexpression has type
% none(). Each top-level definition is typechecked in isolation against its
% spec; if the name ends in _fail, the test must fail.
%
% A call to a function with a known single-arrow type checks the arguments
% against the parameter types and takes the spec's result type directly
% (constr_gen:funcall_constrs_with_tyscm_tyof), instead of constraining the
% function type against (A1, ..., An) -> Beta and leaving the arrow to tally.
% That is the more precise rule -- dropping it costs 50 Ok verdicts on ./src --
% but it does not explore the two alternatives of arrow subtyping that hold
% when the argument product is empty:
%
%   1) the result is checked even though the call can never be evaluated,
%   2) the arguments are checked pointwise rather than as a product.
%
% So the two _fail cases below are false positives, not real type errors. The
% suffix records the current behaviour so a change to the call path cannot flip
% it unnoticed; if they start to pass, the gap was closed and this note should
% go. The shortcut predates the optimization series, it is already in
% ef8fc7352afc.
%
% 21-09-2026 albsch

-spec int_id(integer()) -> integer().
int_id(X) -> X.

-spec int_fst(integer(), boolean()) -> integer().
int_fst(X, _) -> X.

% 1) the call can never be evaluated, but integer() <= atom() is still checked
-spec empty_arg_result_fail() -> atom().
empty_arg_result_fail() -> int_id(erlang:error(nope)).

% 2) the second argument is ill-typed, but the argument product is empty
-spec empty_arg_pointwise_fail() -> integer().
empty_arg_pointwise_fail() -> int_fst(erlang:error(nope), 1).

% Control for 1): same call with a live argument, the result is checked
-spec live_arg_result_fail() -> atom().
live_arg_result_fail() -> int_id(1).

% Control for 2): same call with a live first argument
-spec live_arg_pointwise_fail() -> integer().
live_arg_pointwise_fail() -> int_fst(1, 1).
