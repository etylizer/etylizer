-module(tally).

-export([
  tally/2,
  tally/3,
  is_satisfiable/3
]).

-export_type([monomorphic_variables/0]).

-type monomorphic_variables() :: term().
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, _SubtyConstrs, _Maters, _UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    % cleaning is OK, we only care about one solution
    CleanedConstraints = subst:clean_cons(InternalRawConstraints, FixedVars, SymTab),

    % parse into internal representation
    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- CleanedConstraints],

    % parse variables into internal representation
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    % get internal result
    InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),

    case InternalResult of
        false -> {false, []};
        true -> {true, satisfiable}
    end.

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()) .

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- InternalRawConstraints],

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

    Free = tyutils:free_in_subty_constrs(InlinedConstrs),
    case InternalResult of
        {error, []} -> {error, []};
        _ ->
            % transform to subst:t()
            Sigmas = [subst:mk_tally_subst(
               sets:union(FixedVars, Free),
               maps:from_list([{VarName, ty_parser:unparse(Ty)}
                               || {{var, _, VarName, _}, Ty} <- maps:to_list(Subst)])) % FIXME depends on internal ty_variable representation
             || Subst <- InternalResult],

            lists:map(
              fun({tally_subst, S, Fixed}) ->
                MaterSubst = maps:fold(fun(Var, Ty, MAcc) ->
                    maps:put(Var, subst:apply_base(S, Ty), MAcc)
                  end,
                  #{}, UnificationSubst),
                gradual_utils:postprocess({tally_subst, maps:merge(S, MaterSubst), Fixed}, SubtyConstrs, Maters, SymTab)
              end,
              Sigmas)
      end.
