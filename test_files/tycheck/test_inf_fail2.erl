-module(test_inf_fail2).

-export([
    test/0
]).

% inferred: replicate(integer(), A) -> [A]
replicate(0, _) -> [];
replicate(N, X) -> [X | replicate(N - 1, X)].

-spec foo(list(integer())) -> ok.
foo(_) -> ok.

-spec bar(list(string())) -> ok.
bar(_) -> ok.

-spec test() -> ok.
test() ->
    ok = foo(replicate(5, 1)),
    ok = bar(replicate("X", 3)).
