-module(tally).

-export([
  tally/2,
  tally/3,
  tally/4
]).

tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()) .

tally(SymTab, Constraints, FixedVars) ->
  tally(SymTab, Constraints, FixedVars, fun() -> noop end).

tally(_SymTab, Constraints, FixedVars, Order) ->
  ty_ref:reset(),
  ty_variable:reset(),
  ast_lib:reset(),
  Order(),

  InternalConstraints = lists:map(
    fun({csubty, _, S, T}) -> {ast_lib:ast_to_erlang_ty(S), ast_lib:ast_to_erlang_ty(T)} end,
    lists:sort(fun({csubty, _, S, T}, {csubty, _, X, Y}) -> ({S, T}) < ({X, Y}) end,
      sets:to_list(Constraints))
  ),
  InternalResult = etally:tally(InternalConstraints, sets:from_list([ast_lib:ast_to_erlang_ty_var({var, Var}) || Var <- lists:sort(sets:to_list(FixedVars))])),
%%  io:format(user, "Got Constraints ~n~p~n~p~n", [InternalConstraints, InternalResult]),

  X = case InternalResult of
        {error, []} ->
          {error, []};
        _ ->
          % transform to subst:t()
          % TODO sanity variable Id == variable name
          [maps:from_list([{VarName, ast_lib:erlang_ty_to_ast(Ty)} || {{var, _, VarName}, Ty} <- Subst]) || Subst <- InternalResult]
      end,
  X.
