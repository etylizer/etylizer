-module(tally).

-export([
  tally/2,
  is_satisfiable/3
]).

-ifdef(TEST).
-export([
  tally/3
]).
-endif.


-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).

-spec tally(symtab:t(), constr:subty_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new([{version, 2}])) .

-spec is_satisfiable(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname())) ->
  {false, [{error, string()}]} | {true, subst:t()}. % The substitution is just returned for debugging purpose.
is_satisfiable(SymTab, Constraints, FixedVars) ->
  tally(SymTab, Constraints, FixedVars, satisfiable).

-spec tally(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
  tally(SymTab, Constraints, FixedVars, solve).

-spec tally
  (symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname()), solve) -> tally_res();
  (symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname()), satisfiable) -> {false, [{error, string()}]} | {true, subst:t()}.
tally(SymTab, Constraints, FixedVars, Mode) ->
  % reset the global cache, will be fixed in the future
  ty_ref:reset(),
  ty_variable:reset(),
  ast_lib:reset(),
  ast_to_erlang_ty:reset(),

  % uncomment to extract a tally test case config file
  % io:format(user, "~s~n", [test_utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

  InternalConstraints = lists:map(
    fun({scsubty, _, S, T}) -> {ast_lib:ast_to_erlang_ty(S, SymTab), ast_lib:ast_to_erlang_ty(T, SymTab)} end,
    lists:sort(fun({scsubty, _, S, T}, {scsubty, _, X, Y}) -> ({S, T}) < ({X, Y}) end,
      sets:to_list(Constraints))
  ),
  FixedTallyTyvars =
    [ast_lib:ast_to_erlang_ty_var({var, Var}) || Var <- lists:sort(sets:to_list(FixedVars))],

  case Mode of
    solve ->
      InternalResult = etally:tally(InternalConstraints, sets:from_list(FixedTallyTyvars, [{version, 2}])),
      % io:format(user, "Got Constraints ~n~s~n~p~n", [print(InternalConstraints), InternalResult]),

      Free = tyutils:free_in_subty_constrs(Constraints),
      case InternalResult of
            {error, []} ->
              {error, []};
            _ ->
              % transform to subst:t()
              % TODO sanity variable Id == variable name
              [subst:mk_tally_subst(
                sets:union(FixedVars, Free),
                maps:from_list([{VarName, ast_lib:erlang_ty_to_ast(Ty, #{})}
                              || {{var, _, VarName}, Ty} <- maps:to_list(Subst)]))
              || Subst <- InternalResult]
      end;
    satisfiable ->
      InternalResult = etally:is_tally_satisfiable(InternalConstraints, sets:from_list(FixedTallyTyvars)),

      case InternalResult of
        false -> {false, []};
        true -> {true, subst:empty()}
      end
  end.
% print(Cs) ->
%   "<<" ++ string:join([ty_rec:print(S) ++ " < " ++ ty_rec:print(T) || {S, T} <- Cs], ",\n") ++ ">>".