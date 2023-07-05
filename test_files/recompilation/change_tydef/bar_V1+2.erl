-module(bar).

-export([bar_fun/1]).

-spec bar_fun(integer()) -> integer().
bar_fun(X) -> X+1.

