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

-record(ctx,
        { var_counter :: counters:counters_ref(),
          symtab :: symtab:t()
        }).
-type ctx() :: #ctx{}.

-spec new_ctx(symtab:t()) -> ctx().
new_ctx(Symtab) ->
    Counter = counters:new(2, []),
    Ctx = #ctx{ var_counter = Counter, symtab = Symtab },
    Ctx.

-include("log.hrl").


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

  Ctx = new_ctx(SymTab),
  Pre = preprocess_constrs(Ctx, Constraints),

  InternalConstraints = lists:map(
    fun({scsubty, _, S, T}) -> {ast_lib:ast_to_erlang_ty(S, SymTab), ast_lib:ast_to_erlang_ty(T, SymTab)} end,
    lists:sort(fun({scsubty, _, S, T}, {scsubty, _, X, Y}) -> ({S, T}) < ({X, Y}) end,
      sets:to_list(Pre))
  ),
  FixedTallyTyvars =
    [ast_lib:ast_to_erlang_ty_var({var, Var}) || Var <- lists:sort(sets:to_list(FixedVars))],

  case Mode of
    solve ->
      InternalResult = etally:tally(InternalConstraints, sets:from_list(FixedTallyTyvars, [{version, 2}])),
      % io:format(user, "Got Constraints ~n~s~n~p~n", [print(InternalConstraints), InternalResult]),

      Free = tyutils:free_in_subty_constrs(Pre),
      case InternalResult of
            {error, []} ->
              {error, []};
            _ ->
              % transform to subst:t()
              % TODO sanity variable Id == variable name
              Sigma = [subst:mk_tally_subst(
                sets:union(FixedVars, Free),
                maps:from_list([{VarName, ast_lib:erlang_ty_to_ast(Ty, #{})}
                              || {{var, _, VarName}, Ty} <- maps:to_list(Subst)]))
              || Subst <- InternalResult],
              ?LOG_DEBUG("Got Sigma: ~s", pretty:render_substs(Sigma)),

              Alphas = collect_typevars (Sigma, Pre, FixedVars),
              FVars = collect_framevars(Sigma),
              FVarSubsts = lists:foldl(
                fun(X, Acc) ->
                  maps:put(X, fresh_typevar_name(Ctx), Acc)
                end,
                #{},
                lists:usort(FVars)
              ),
              ?LOG_DEBUG("Got FVarSubsts: ~p", FVarSubsts),
              AlphaSubsts = sets:fold(
                fun(X, Acc) ->
                  maps:put(X, fresh_framevar_name(Ctx), Acc)
                end,
                #{},
                Alphas
              ),
              ?LOG_DEBUG("Got AlphaSubsts: ~p", AlphaSubsts),
              Sigma2 = maps:merge(FVarSubsts, AlphaSubsts),
              ?LOG_DEBUG("Got Sigma2: ~p", Sigma2),
              Res = postprocess_substs(Sigma, Sigma2),
              ?LOG_DEBUG("Got result: ~s", pretty:render_substs(Res)),
              Res
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


%--------------------------------------------------------
% Tally pre- and postprocessing
% -------------------------------------------------------

% TODO: Optimize code  

-spec fresh_typevar_name(ctx()) -> ast:ty_varname().
fresh_typevar_name(Ctx) ->
    I = counters:get(Ctx#ctx.var_counter, 1),
    counters:add(Ctx#ctx.var_counter, 1, 1),
    S = utils:sformat("$post_%~w", I),
    list_to_atom(S).

-spec fresh_framevar_name(ctx()) -> ast:ty_varname().
fresh_framevar_name(Ctx) ->
    I = counters:get(Ctx#ctx.var_counter, 1),
    counters:add(Ctx#ctx.var_counter, 1, 1),
    S = utils:sformat("%~w", I),
    list_to_atom(S).

-spec fresh_framevar(ctx()) -> ast:ty_var().
fresh_framevar(Ctx) ->
    X = fresh_framevar_name(Ctx),
    {var, X}.

% When we see a gradual type with {predef, dynamic}
% we replace each dynamic with a fresh frame variable
-spec preprocess_constrs(ctx(), constr:subty_constrs()) -> constr:subty_constrs().
preprocess_constrs(Ctx, Constrs) ->
    List = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, Acc) ->
                case {is_dynamic(T1), is_dynamic(T2)} of
                    {true, true} -> [{scsubty, Loc, fresh_framevar(Ctx), fresh_framevar(Ctx)} | Acc];
                    {true, _} -> [{scsubty, Loc, fresh_framevar(Ctx), T2} | Acc];
                    {_, true} -> [{scsubty, Loc, T1, fresh_framevar(Ctx)} | Acc];
                    _ -> [{scsubty, Loc, T1, T2} | Acc]
                end;
            ({scmater, Loc, _T1, T2}, Acc) ->
                [{scsubty, Loc, fresh_framevar(Ctx), {var, T2}} | Acc];
            (Constr, Acc) ->
                [Constr | Acc]
        end,
        [],
        Constrs),
    ?LOG_DEBUG("Preprocessed constraints for gradual typing:~n~s",
        pretty:render_constr(List)),
    sets:from_list(List, [{version,2}]).

-spec is_dynamic(ast:ty()) -> boolean().
is_dynamic({predef, dynamic}) -> true;
is_dynamic(_) -> false.

-spec postprocess_substs([subst:t()], #{ast:ty_varname() => ast:ty_varname()}) -> [subst:t()].
postprocess_substs(Sigma, Sigma2) ->
    lists:map(
        fun({tally_subst, S, Fixed}) ->
            S1 = apply_subst(S, Sigma2),
            {tally_subst, S1, sets:union(Fixed, sets:from_list(maps:values(Sigma2), [{version, 2}]))}
        end,
        Sigma
     ).

-spec apply_subst(subst:t(), #{ast:ty_varname() => ast:ty_varname()}) -> subst:t().
apply_subst(S, Sigma2) ->
    maps:fold(
        fun(Var, Ty, Acc) ->
            maps:put(Var, subst_ty(Ty, Sigma2), Acc)
        end,
        S,
        S).

-spec subst_ty(ast:ty(), #{ast:ty_varname() => ast:ty_varname()}) -> ast:ty().
subst_ty(Ty, VarSubst) ->
    case Ty of
        {var, Name} ->
            case maps:find(Name, VarSubst) of
                {ok, NewName} -> {var, NewName};
                error -> Ty
            end;
        {union, Args} -> {union, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args)};
        {intersection, Args} -> {intersection, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args)};
        {fun_full, Args, RetTy} -> {fun_full, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args), subst_ty(RetTy, VarSubst)};
        _ -> Ty
    end.

-spec collect_typevars([subst:t()], constr:subty_constrs(), sets:set(ast:ty_varname())) -> sets:set(ast:ty_varname()).
collect_typevars(Sigma, Constrs, FixedVars) ->
  CollectFun = fun(X) -> case X of
    {var, Alpha} -> 
      case is_typevar(Alpha) of
        true -> {ok, Alpha};
        false -> error
      end;
    _ -> error
    end
  end,
  Var_D = lists:usort(
    lists:foldl(
      fun({scsubty, _, T1, T2}, Acc) ->
        utils:everything(CollectFun, T1) ++ utils:everything(CollectFun, T2) ++ Acc
      end,
      [],
      sets:to_list(Constrs)
    )
  ),
  ?LOG_DEBUG("Got Var_D: ~p", Var_D),
  ?LOG_DEBUG("Got FixedVars: ~p", FixedVars),
  Dom_Sigma = lists:foldl(
    fun({tally_subst, S, _}, Acc) ->
      lists:filter(fun(X) -> is_typevar(X) end, maps:keys(S)) ++ Acc
    end,
    [],
    Sigma
  ),
  ?LOG_DEBUG("Got Dom_Sigma: ~p", Dom_Sigma),
  Var_Substs = lists:foldl(
    fun({tally_subst, S, _}, Acc) ->
      lists:foldl(
        fun(Ty, Acc2) ->
          utils:everything(CollectFun, Ty) ++ Acc2
        end,
        [],
        maps:values(S)
      ) ++ Acc
    end,
    [],
    Sigma
  ),
  ?LOG_DEBUG("Got Var_Substs: ~p", Var_Substs),
  % α = var(D)∖(Δ ∪ dom(σ0​) ∪ var⊑(D)σ0​)
  Alphas = sets:subtract(sets:from_list(Var_D, [{version, 2}]),
            sets:from_list(sets:to_list(FixedVars) ++ Dom_Sigma ++ Var_Substs, [{version, 2}])),
  ?LOG_DEBUG("Got Alphas: ~p", Alphas),
  Alphas.

-spec collect_framevars([subst:t()]) -> sets:set(ast:ty_varname()).
collect_framevars(Sigma) ->
  CollectFun = fun(X) -> case X of
    {var, Alpha} -> 
      case is_framevar(Alpha) of
        true -> {ok, Alpha};
        false -> error
      end;
    _ -> error
    end
  end,
  FVars = lists:foldl(
    fun({tally_subst, S, _}, Acc) ->
      lists:foldl(
        fun(Ty, Acc2) ->
          utils:everything(CollectFun, Ty) ++ Acc2
        end,
        [],
        maps:values(S)
      ) ++ Acc
    end,
    [],
    Sigma
  ),
  ?LOG_DEBUG("Got FVars: ~p", FVars),
  FVars.

-spec is_framevar(ast:ty_varname()) -> boolean().
is_framevar(Name) -> starts_with(Name, "%").

-spec is_typevar(ast:ty_varname()) -> boolean().
is_typevar(Name) -> starts_with(Name, "$").

-spec starts_with(ast:ty_varname(), string()) -> boolean().
starts_with(Name, Prefix) ->
    case string:prefix(atom_to_list(Name), Prefix) of
        nomatch -> false;
        _ -> true
    end.
