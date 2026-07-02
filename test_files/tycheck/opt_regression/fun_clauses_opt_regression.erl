-module(fun_clauses_opt_regression).

-compile([export_all, nowarn_export_all]).

%% Inference regression test for one of the optimizations.

-export([go/0]).

-spec go() -> ok.
go() -> ok.

merge(Inner, Outer) ->
    maps:fold(
      fun(V, {_, _, InnerNPols}, OuterAcc) ->
              Doubled = InnerNPols ++ [1 - P || P <- InnerNPols],
              maps:update_with(V,
                  fun({Ups, Lows, NPols}) -> {Ups, Lows, Doubled ++ NPols} end,
                  {[], [], Doubled}, OuterAcc)
      end, Outer, Inner).
