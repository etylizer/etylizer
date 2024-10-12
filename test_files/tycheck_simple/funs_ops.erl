-module(funs_ops).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% SIMPLE FUNCTIONS %%%%%%%%%%%%%%%%%%%%%%%

-spec fun_01(any()) -> any().
fun_01(X) -> X.

-spec fun_02_fail(integer()) -> atom().
fun_02_fail(X) -> X.

-spec fun_03(string(), integer()) -> integer().
fun_03(_X, Y) -> Y.

-spec fun_04_fail(string(), integer()) -> integer().
fun_04_fail(X, _Y) -> X.

-spec fun_05(integer()) -> any().
fun_05(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% FUNCTION CALLS %%%%%%%%%%%%%%%%%%%%%%%

-spec some_fun(string(), integer()) -> string().
some_fun(S, _) -> S.

-spec fun_ref_01() -> string().
fun_ref_01() -> some_fun("foo", 42).

-spec fun_ref_02_fail() -> integer().
fun_ref_02_fail() -> some_fun("foo", 42).

-spec fun_ref_03_fail() -> string().
fun_ref_03_fail() -> some_fun("foo", "42").

%%%%%%%%%%%%%%%%%%%%%%%% OPERATORS %%%%%%%%%%%%%%%%%%%%%%%

-spec op_01() -> integer().
op_01() -> 1 + 2.

-spec op_02() -> boolean().
op_02() -> 1 =:= 2.

-spec op_03() -> integer().
op_03() -> -3.

% fails in gradualizer with
% "The integer on line 147 at column 13 is expected to have type integer but it has type 1"
-spec op_04() -> list(integer()).
op_04() -> [1,2] ++ [3,4].

-spec op_05() -> boolean().
op_05() -> 1 =:= "foo".

-spec op_06_fail(integer()) -> boolean().
op_06_fail(X) -> X + "foo".

-spec op_07_fail() -> list(integer()).
op_07_fail() -> [1,2] ++ ["foo", "bar"].

-spec op_08() -> list().
op_08() -> [1,2] ++ ["foo", "bar"].

-spec op_09() -> list(integer()).
op_09() -> [] ++ [].

-spec op_10_fail() -> 0.
op_10_fail() -> -1.

-spec op_11() -> false.
op_11() -> false andalso no.

-spec op_12() -> true.
op_12() -> true orelse no.

-spec op_13_fail() -> boolean().
op_13_fail() -> true andalso no.

-spec op_14_fail() -> boolean().
op_14_fail() -> false orelse no.
