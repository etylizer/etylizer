-module(exported_vs_local).

-export([exported_function/1]).
-export_type([exported_type/0]).

-type local_type() :: boolean().

-type exported_type() :: integer() | string() | atom().

-spec local_function(integer()) -> integer().
local_function(X) ->
    2 * X.

-spec exported_function(integer()) -> integer().
exported_function(X) ->
    4 * X.
