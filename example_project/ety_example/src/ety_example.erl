-module(ety_example).

-compile([export_all, nowarn_export_all]).

-spec fun0() -> integer().
fun0() -> 2.

-spec fun1() -> bad.
fun1() -> ok.

-spec fun2() -> bad.
fun2() -> try bad catch _ -> bad end.

% internal module calls
-spec fun4() -> number().
fun4() ->
    fun0().

% internal module calls (issue #270)
-spec fun5() -> number().
fun5() ->
    ety_example:fun4().

% likely a timeout: too many function applications of intersections of function types
-spec fun_timeout() -> integer().
fun_timeout() -> 
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.

% type error until #122 (refinement for =:=) is fixed, workaround see f2
-spec f(integer() | [integer()] | none) -> number().
f([_|_] = Ints) -> lists:sum(Ints);
f(EmptyOrNone) when EmptyOrNone =:= none orelse is_list(EmptyOrNone) -> 0;
f(Int) -> Int.

% external module calls are supported
-spec f2(integer() | [integer()] | none) -> number().
f2([_|_] = Ints) -> lists:sum(Ints);
f2(none) -> 0;
f2(Empty) when is_list(Empty) -> 0;
f2(Int) -> Int.

% local functions
-spec f3() -> number().
f3() ->
    L1 = [1,2],
    L2 = [3,a],
    Z = fun(L, LL) -> lists:sum(L) + lists:sum(LL) end,
    Z(L1, L2).

% distributivity laws supported
-spec dist({ok | err, arg | nil}) -> {ok, arg} | {err, arg} | {ok, nil} | {err, nil}.
dist(X) -> X.

% occurrence typing and intersection types
-spec inter_01 (integer()) -> integer(); (atom()) -> atom().
inter_01(X) -> 
    case X of
        _ when is_integer(X) -> X + 1;
        _ -> X
    end.
