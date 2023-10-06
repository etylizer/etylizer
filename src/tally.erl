-module(tally).

-export([
  tally/2,
  tally/3
]).

tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()) .

tally(_SymTab, Constraints, FixedVars) ->
  InternalConstraints = lists:map(fun({csubty, _, S, T}) ->
%%    io:format(user, "~p~n", [{S, T}]),
    {ast_lib:ast_to_erlang_ty(S), ast_lib:ast_to_erlang_ty(T)} end, sets:to_list(Constraints)),
  InternalResult = etally:tally(InternalConstraints, sets:from_list([ast_lib:ast_to_erlang_ty_var({var, Var}) || Var <- sets:to_list(FixedVars)])),
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