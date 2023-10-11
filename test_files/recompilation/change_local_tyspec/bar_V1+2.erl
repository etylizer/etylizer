-module(bar).

-export([bar_fun/1]).

-spec bar_fun(boolean()) -> boolean().
bar_fun(X) -> X and true.

