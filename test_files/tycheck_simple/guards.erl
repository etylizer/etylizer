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
