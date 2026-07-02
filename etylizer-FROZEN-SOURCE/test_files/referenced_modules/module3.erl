
-module(module3).
-export([fun3/1]).

-spec fun3(int) -> int.
fun3(X) ->
    3 * X.
