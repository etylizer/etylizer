-module(pattern_refine).

-include_lib("eunit/include/eunit.hrl").

-spec foo(integer()) -> integer().
foo(X) -> X + 1.

-spec bar(integer() | true) -> integer().
bar(X) ->
    case X of
        true -> 1;
        _ -> foo(X) % gradualizer fails here
    end.

my_test() ->
    ?assertEqual(1, bar(true)),
    ?assertEqual(6, bar(5)).
