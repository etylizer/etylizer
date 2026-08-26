-module(fun_clauses_opt_regression_fail).

%% Inference regression test for one of the optimizations.
%% Here go/1 returns a list but is spec'd to return integer().

-export([go/1]).

-spec go([{atom(), list()}]) -> integer().
go(Pairs) ->
    lists:foldl(fun({_K, Xs}, Acc) -> [Xs | Acc] end, [], Pairs).
