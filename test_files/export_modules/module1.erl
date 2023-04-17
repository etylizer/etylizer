
-module(module1).
-export([fun1/1]).

-spec fun1(int) -> int.
fun1(X) ->
    module2:fun2(X) + module3:fun3(X) + test_fun(23).

-spec test_fun(int) -> int.
test_fun(Y) ->
    2 * Y.
