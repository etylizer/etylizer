-module(funs_ops).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-spec down(dynamic()) -> integer().
down(X) -> X.

-spec up(integer()) -> dynamic().
up(X) -> X.

-spec fun_down(fun((integer()) -> dynamic())) -> fun((integer()) -> atom()).
fun_down(X) -> X.

-spec fun_down_fail(fun((integer()) -> dynamic())) -> fun((string()) -> atom()).
fun_down_fail(X) -> X.

-spec fun_down2(fun((dynamic()) -> atom())) -> fun((integer()) -> atom()).
fun_down2(X) -> X.

-spec fun_up(fun((integer()) -> atom())) -> fun((integer()) -> dynamic()).
fun_up(X) -> X.

-spec fun_up_fail(fun((integer()) -> atom())) -> fun((string()) -> dynamic()).
fun_up_fail(X) -> X.

-spec fun_up2(fun((integer()) -> atom())) -> fun((dynamic()) -> atom()).
fun_up2(X) -> X.

-spec fun_mixed(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((integer(), dynamic(), float()) -> {dynamic(), integer()}).
fun_mixed(X) -> X.

-spec fun_mixed_fail(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((integer(), dynamic(), float()) -> {float(), integer()}).
fun_mixed_fail(X) -> X.

-spec fun_mixed2_fail(fun((integer(), string(), dynamic()) -> {atom(), dynamic()})) ->
    fun((atom(), dynamic(), float()) -> {dynamic(), integer()}).
fun_mixed2_fail(X) -> X.

-spec list_down(list(dynamic())) -> list(integer()).
list_down(X) -> X.

-spec list_up(list(integer())) -> list(dynamic()).
list_up(X) -> X.

-spec tuple_down({integer(), dynamic(), atom()}) -> {integer(), string(), atom()}.
tuple_down(X) -> X.

-spec tuple_down_fail({integer(), dynamic(), atom()}) -> {integer(), string(), float()}.
tuple_down_fail(X) -> X.

-spec tuple_up({integer(), string(), atom()}) -> {integer(), dynamic(), atom()}.
tuple_up(X) -> X.

-spec tuple_up_fail({integer(), string(), atom()}) -> {integer(), dynamic(), float()}.
tuple_up_fail(X) -> X.

-spec tuple_up_down({dynamic(), string(), atom()}) -> {integer(), dynamic(), atom()}.
tuple_up_down(X) -> X.

-spec tuple_up_down_fail({dynamic(), string(), atom()}) -> {integer(), dynamic(), float()}.
tuple_up_down_fail(X) -> X.
