-module(no_change).

-export([exported_fun/1]).

-spec exported_fun(integer()) -> integer().
exported_fun(X) -> X * 4.
