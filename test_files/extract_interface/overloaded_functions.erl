-module(overloaded_functions).

-export([exported_function/1, exported_function/2]).
-export_type([foo/1, foo/2]).

-type foo(T) :: T.
-type foo(K, V) :: {K, V}.
-type foo(K, V, U) :: {K, V, U}.

-spec exported_function(integer()) -> integer().
exported_function(X) ->
    X.

-spec exported_function(integer(), integer()) -> integer().
exported_function(X, Y) ->
    X + Y.

-spec exported_function(integer(), integer(), integer()) -> integer().
exported_function(X, Y, Z) ->
    X + Y + Z.
