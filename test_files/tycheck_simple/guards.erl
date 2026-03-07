-module(guards).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% GUARDS %%%%%%%%%%%%%%%%%%%%%%%

-spec guard_01(fun((none()) -> term())) -> ok.
guard_01(F) when is_function(F, 1) -> ok.

-spec guard_02(fun((term()) -> term())) -> ok.
guard_02(F) when is_function(F, 1) -> ok.

-spec guard_03(fun((_) -> term())) -> ok.
guard_03(F) when is_function(F, 1) -> ok.

-spec guard_04(fun((_) -> _)) -> ok.
guard_04(F) when is_function(F, 1) -> ok.

-spec guard_05(fun((_, _) -> _)) -> ok.
guard_05(F) when is_function(F, 2) -> ok.

-spec guard_06
    (fun((_) -> _)) -> ok;
    (fun((_, _) -> _)) -> ok.
guard_06(F) when is_function(F, 1) -> ok;
guard_06(F) when is_function(F, 2) -> ok.

-spec guard_07(fun((none()) -> term())) -> ok.
guard_07(F) when is_function(F) -> ok.

-spec guard_08
    (fun((_) -> _)) -> ok;
    (fun((_, _) -> _)) -> ok.
guard_08(F) when is_function(F) -> ok.

-spec guard_09_fail
    (fun((_) -> _)) -> ok;
    (fun((_, _) -> _)) -> ok.
guard_09_fail(F) when is_function(F, 2) -> ok.

-spec guard_10_fail(fun((term()) -> term())) -> ok.
guard_10_fail(F) when is_function(F, 2) -> ok.

-spec guard_variable_name_01({atom() | integer(), atom() | integer()}) -> atom().
guard_variable_name_01({A1, A2}) when is_atom(A1), is_atom(A2) -> A1;
guard_variable_name_01({_, _}) -> ok.

-spec guard_variable_name_02({atom() | integer(), atom() | integer()}) -> atom().
guard_variable_name_02({ZZ1, ZZ2}) when is_atom(ZZ1), is_atom(ZZ2) -> ZZ1;
guard_variable_name_02({_, _}) -> ok.

% Guard narrowing with 'or': when the or-guard fails, 
% the negation 
%   not(is_atom(X) or is_atom(Y)) 
% which is equal to
%   not is_atom(X) and not is_atom(Y)
% should narrow both X and Y to integer() in clause 2.
-spec guard_or_narrow_01({atom() | integer(), atom() | integer()}) -> integer().
guard_or_narrow_01({_X, _Y}) when is_atom(_X) or is_atom(_Y) -> 0;
guard_or_narrow_01({X, Y}) -> X + Y.

% Unsound union_envs for or-guards with non-overlapping keys:
% is_atom(X) or is_atom(Y) only guarantees that ONE of them is an atom,
% but the current union_envs refines BOTH to atom. This test should fail
% because Y could be integer when X is the atom (and vice versa).
-spec guard_or_unsound_01_fail({atom() | integer(), atom() | integer()}) -> {atom(), atom()}.
guard_or_unsound_01_fail({X, Y}) when is_atom(X) or is_atom(Y) -> {X, Y};
guard_or_unsound_01_fail({_, _}) -> {a, b}.

% Guard refinement of an outer-scope variable in a case expression.
% The guard is_integer(X) refines X (from the function args), not the
% scrutiny Y. Upper cannot capture this because X is not bound by the
% case pattern, so guard_seq_env in pat_guard_env is the sole source.
% This tests that combine_guard_result does not lose refinements
% when folding over a single guard sequence.
-spec guard_outer_refine_01(atom() | integer(), term()) -> integer().
guard_outer_refine_01(X, Y) ->
    case Y of
        _ when is_integer(X) -> X;
        _ -> 0
    end.

% not(is_atom(X) orelse is_atom(Y)) should narrow X and Y to ¬atom.
% With input {integer(), integer()}, the guard always succeeds, so the
% first branch must be alive. Currently guard_test_lower_envs does not
% handle 'not', falling through to guard_test_env which unions the two
% or-branches ({X=>atom} ∪ {Y=>atom} = {X=>any,Y=>any}) and negates
% to {X=>none,Y=>none}, making the branch appear dead.
% The intersection type exposes this: branch 1 is correctly dead for
% spec 1 ({atom,atom}) but should be alive for spec 2 ({integer,integer}).
% The bug makes it dead in both → unmatched in all intersections → error.
-spec guard_not_or_precise_01({atom(), atom()}) -> atom(); ({integer(), integer()}) -> integer().
guard_not_or_precise_01({X, Y}) when not (is_atom(X) orelse is_atom(Y)) -> X + Y;
guard_not_or_precise_01({X, _}) -> X.
