-module(extract_interface_test).

-export([exported_function/2]).
-export_type([exported_type_1/0, exported_type_2/0]).

-type local_type_1() :: map() | tuple().
-type local_type_2() :: local_type_1() | integer().
-type local_type_3() :: boolean().

-type exported_type_1() :: integer() | string() | atom().
-type exported_type_2() :: file:filename() | local_type_1().

-spec local_function(integer()) -> integer().
local_function(X) ->
    2 * X.

-spec exported_function(integer(), local_type_2()) -> integer().
exported_function(X, Y) ->
    4 * X + Y.
