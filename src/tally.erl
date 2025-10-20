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

-export_type([monomorphic_variables/0]).


-type monomorphic_variables() :: term().
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).

-spec tally(symtab:t(), constr:subty_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()) .

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

  % uncomment to extract a tally test case config file
  %io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),
  
  % erlang_types has a global symtab
  ty_parser:set_symtab(SymTab),

  InternalConstraints = 
    lists:map( fun ({scsubty, _, S, T}) -> {ty_parser:parse(S), ty_parser:parse(T)} end,
      lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) -> (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
        sets:to_list(Constraints))
    ),
  MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

  case Mode of
    solve ->
      InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

      Free = tyutils:free_in_subty_constrs(Constraints),
      case InternalResult of
            {error, []} ->
              {error, []};
            _ ->
              % transform to subst:t()
              [subst:mk_tally_subst(
                sets:union(FixedVars, Free),
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
