-module(match2).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec foo(list()) -> integer().
foo(X) ->
    [ _ | _ ] = X,
    length(X). % X has type list() here

my_test() ->
    ?assertEqual(2, foo([1,2])).
