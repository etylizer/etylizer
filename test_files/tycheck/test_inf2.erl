-module(test_inf2).

-export([
    test/0
]).

% inferred: replicate(integer(), A) -> [A]
replicate(0, _) -> [];
replicate(N, X) -> [X | replicate(N - 1, X)].

% some_other_fun is not in the same group of mutually recursive functions
% as replicate. Hence, the type of replicate is generalized and not fixed
% by the invoation in some_other_fun.
some_other_fun() -> replicate(1,2).

-spec foo(list(integer())) -> ok.
foo(_) -> ok.

-spec bar(list(string())) -> ok.
bar(_) -> ok.

-spec test() -> ok.
test() ->
    ok = foo(replicate(5, 1)),
    ok = bar(replicate(3, "X")).
