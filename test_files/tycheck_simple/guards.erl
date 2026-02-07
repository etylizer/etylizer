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

-spec refinement_01(integer()) -> 1.
refinement_01(X) ->
    case X of
        _ when X < 1 -> 1;
        _ when X > 1 -> 1;
        _ -> X
    end.

-spec refinement_01b(integer()) -> 1.
refinement_01b(X) ->
    if X < 1 -> 1;
       X > 1 -> 1;
       true -> X
    end.

-spec refinement_01c(integer()) -> 1.
refinement_01c(X) ->
    case {} of
        _ when X < 1 -> 1;
        _ when X > 1 -> 1;
        _ -> X
    end.

-spec refinement_02(do) -> integer().
refinement_02(Do) when Do =:= do -> 0.

-spec refinement_03(integer()) -> non_neg_integer().
refinement_03(X) when X > 0 -> X;
refinement_03(_) -> 0.

-spec refinement_04_fail(integer()) -> non_neg_integer().
refinement_04_fail(X) when X > 0 -> X.

-spec refinement_05(integer()) -> non_neg_integer().
refinement_05(X) when X > 0 -> X;
refinement_05(X) when not(X > 0) -> 0.

-spec refinement_06(float()) -> float().
refinement_06(X) when not(X > 0.5) -> X;
refinement_06(X) -> 5.0.
