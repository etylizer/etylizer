% ERROR
% The following exported functions have no type specification: foo/1
-module(invalid_export).
-export([foo/1, bar/1]).

foo(X) ->
    X + 1.

-spec bar(integer()) -> integer().
bar(X) ->
    X - 1.
