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



% -type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).

% -spec tally(symtab:t(), constr:subty_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, _MonomorphicVariables = #{}) .

% -spec is_satisfiable(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname())) ->
%   {false, [{error, string()}]} | {true, subst:t()}. % The substitution is just returned for debugging purpose.
is_satisfiable(SymTab, Constraints, MonomorphicVariables) ->
  tally(SymTab, Constraints, MonomorphicVariables, satisfiable).

% -spec tally(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, MonomorphicVariables) ->
  tally(SymTab, Constraints, MonomorphicVariables, solve).

% -spec tally
%   (symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname()), solve) -> tally_res();
%   (symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname()), satisfiable) -> {false, [{error, string()}]} | {true, subst:t()}.
tally(_SymTab, Constraints, MonomorphicVariables, Mode) ->
  % uncomment to extract a tally test case config file
  % io:format(user, "~s~n", [test_utils:format_tally_config(sets:to_list(Constraints), MonomorphicVariables, SymTab)]),
  
  % 1. Extend symtab symbols
  % TODO
  
  % io:format(user,"Input:~n~p~n", [Constraints]),

  % 2. Parse constraints into internal representation
  % io:format(user,"Parsing constraints:~n~p~n", [sets:to_list(Constraints)]),
  % TODO sort by complexity instead
  InternalConstraints = 
  lists:map(
    fun ({scsubty, _, S, T}) -> 
        {ty_parser:parse(S), ty_parser:parse(T)} end,
    lists:sort(
      fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) -> (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
      sets:to_list(Constraints))
  ),

  io:format(user,"MonomorphicVariables: ~p (is set ~p)~n", [MonomorphicVariables, sets:is_set(MonomorphicVariables)]),
  MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(MonomorphicVariables)]),
  io:format(user,"MonomorphicVariables: ~p~n", [MonomorphicTallyVariables]),

  case Mode of
    solve ->
      % io:format(user,"Vars: ~p~n", [MonomorphicTallyVariables]),
      InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),
      io:format(user,"Solution: ~p~n", [InternalResult]),

      % % io:format(user, "Got Constraints ~n~s~n~p~n", [print(InternalConstraints), InternalResult]),

      Free = free_in_subty_constrs(Constraints),
      case InternalResult of
            {error, []} -> {error, []};
            _ ->
              [mk_tally_subst(
                sets:union(MonomorphicVariables, Free),
                maps:from_list([{VarName, ty_parser:unparse(Ty)}
                              || {{var, _, VarName}, Ty} <- maps:to_list(Subst)]))
              || Subst <- InternalResult]
      end;
    satisfiable ->
      InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),

      case InternalResult of
        false -> {false, []};
        true -> {true, subst:empty()}
      end
  end.

free_in_subty_constrs(Cs) ->
    sets:fold(
        fun (C, Acc) -> sets:union(Acc, free_in_subty_constr(C)) end,
        sets:new([{version, 2}]),
        Cs).

free_in_subty_constr(C) ->
    case C of
        {scsubty, _Locs, T1, T2} -> sets:union(free_in_ty(T1), free_in_ty(T2))
    end.

mk_tally_subst(Fixed, Base) -> {tally_subst, Base, Fixed}.

free_in_ty(T) ->
    L = utils:everything(fun (U) ->
                                 case U of
                                     {var, X} -> {ok, X};
                                     _ -> error
                                 end
                         end, T),
    sets:from_list(L, [{version, 2}]).
