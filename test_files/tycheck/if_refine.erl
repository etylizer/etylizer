-module(if_refine).

-include_lib("eunit/include/eunit.hrl").

-spec bar(integer()) -> 0..10.
bar(X) ->
    if X < 0 -> 0;
       X > 10 -> 10;
       true -> X
    end.

my_test() ->
    ?assertEqual(0, bar(-1)).
