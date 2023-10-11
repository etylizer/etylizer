-module(no_change).

-export([exported_fun/1]).

-type my_type() :: {ok, integer()}.

-spec local_fun(my_type()) -> integer().
local_fun({ok, X}) -> X + 1.

-spec exported_fun(integer()) -> integer().
exported_fun(X) -> local_fun(X).
