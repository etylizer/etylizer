
-module(module2).
-export([fun2/1]).

-spec fun2(int) -> int.
fun2(X) ->
    module3:fun3(X).
