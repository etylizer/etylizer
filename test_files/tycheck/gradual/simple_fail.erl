-module(simple_fail).

-export([main_fail/0]).

-spec add(integer(), integer()) -> integer().
add(X, Y) ->
    X + Y.

-spec as_string(dynamic()) -> string().
as_string(X) -> X.

-spec main_fail() -> ok.
main_fail() ->
    add(0, as_string(2)),
    ok.

