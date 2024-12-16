
-module(module1).
-export([fun1/1]).

-import(module4, [add/2]).

-spec fun1(int) -> module5:blub().
fun1(X) ->
    module2:fun2(X) + module3:fun3(X) + test_fun(23) + add(X, 4).

-spec test_fun(int) -> int.
test_fun(Y) ->
    2 * Y.
