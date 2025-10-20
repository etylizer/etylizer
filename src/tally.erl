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

-include("log.hrl").

-export_type([monomorphic_variables/0]).


-type monomorphic_variables() :: term().
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).

new_ctx(Symtab) ->
    Counter = counters:new(2, []),
    Ctx = #ctx{ var_counter = Counter, symtab = Symtab },
    Ctx.


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

  Ctx = new_ctx(SymTab),
  {PreConstrs, Maters} = preprocess_constrs(Ctx, Constraints),
  UnificationSubsts = maps:from_list(lists:map(fun({scsubty, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))),
  ?LOG_DEBUG("UnificationSubsts: ~p", UnificationSubsts),
  Pre = sets:map(fun(Constr) -> 
    case Constr of
      {scsubty, _Loc, T1, T2} -> 
        NewT1 = case maps:find(T1, UnificationSubsts) of
          {ok, Tau} -> Tau;
          error -> T1
        end,
        NewT2 = case maps:find(T2, UnificationSubsts) of
          {ok, Tau2} -> Tau2;
          error -> T2
        end,
        {scsubty, _Loc, NewT1, NewT2};
      Other -> Other
    end
  end, PreConstrs),
  ?LOG_DEBUG("Constraints to be sent to Tally:~n~s", pretty:render_constr(Pre)),

  InternalConstraints = 
    lists:map( fun ({scsubty, _, S, T}) -> {ty_parser:parse(S), ty_parser:parse(T)} end,
      lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) -> (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
        sets:to_list(Constraints))
    ),
  MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

  case Mode of
    solve ->
      InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

      Free = tyutils:free_in_subty_constrs(Pre),
      case InternalResult of
            {error, []} ->
              {error, []};
            _ ->
              % transform to subst:t()
              Sigmas = [subst:mk_tally_subst(
                sets:union(FixedVars, Free),
                maps:from_list([{VarName, ty_parser:unparse(Ty)}
                              || {{var, _, VarName}, Ty} <- maps:to_list(Subst)]))
              || Subst <- InternalResult],
              ?LOG_DEBUG("Got Sigma: ~s", pretty:render_substs(Sigmas)),
              
              lists:map(
                fun(Sigma) -> 
                  Post = postprocess(Ctx, Sigma, PreConstrs, Maters),
                  ?LOG_DEBUG("After postprocessing: ~s", pretty:render_subst(Post)),
                  Post
                end,
                Sigmas
              )
      end;
    satisfiable ->
      InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),

      case InternalResult of
        false -> {false, []};
        true -> {true, subst:empty()}
      end
  end.

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
-spec preprocess_constrs(ctx(), constr:subty_constrs()) -> {constr:subty_constrs(), constr:subty_constrs()}.
preprocess_constrs(Ctx, Constrs) ->
    {Subtys, Maters} = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Maters}) ->
              {[{scsubty, Loc, replace_dynamic(T1, Ctx), replace_dynamic(T2, Ctx)} | Cs], Maters};
            ({scmater, Loc, _T1, T2}, {Cs, Maters}) ->
              {Cs, [{scsubty, Loc, fresh_framevar(Ctx), {var, T2}} | Maters]};
            (Constr, {Cs, Maters}) ->
              {[Constr | Cs], Maters}
        end,
        {[], []},
        Constrs),
    
    ?LOG_DEBUG("Preprocessed constraints for gradual typing:~n~p",
        Subtys),
    {sets:from_list(Subtys, [{version,2}]), sets:from_list(Maters, [{version,2}])}.

-spec replace_dynamic(ast:ty(), ctx()) -> ast:ty().
replace_dynamic({predef, dynamic}, Ctx) -> fresh_framevar(Ctx);
replace_dynamic({var, Name}, _Ctx) -> {var, Name};
replace_dynamic({union, Types}, Ctx) -> {union, lists:map(fun(T) -> replace_dynamic(T, Ctx) end, Types)};
replace_dynamic({intersection, Types}, Ctx) -> {intersection, lists:map(fun(T) -> replace_dynamic(T, Ctx) end, Types)};
replace_dynamic({fun_full, ArgTypes, RetType}, Ctx) ->
    {fun_full, lists:map(fun(T) -> replace_dynamic(T, Ctx) end, ArgTypes), replace_dynamic(RetType, Ctx)};
replace_dynamic({list, Ty}, Ctx) -> {list, replace_dynamic(Ty, Ctx)};
replace_dynamic(Ty, _Ctx) -> Ty.


% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(ctx(), subst:t(), constr:subty_constrs(), constr:subty_constrs()) -> subst:t().
postprocess(Ctx, {tally_subst, S, Fixed}, Constrs, Maters) ->
    % Step 3b): find all type variables appearing in the gradual types in materialization constraints
    % and substitute them with the found tally solution 
    TypeVarsInMaters = sets:fold(
        fun({scsubty, _, Tau, _}, Acc) ->
          CollectFun = fun(X) -> case X of
            {var, Alpha} -> case is_typevar(Alpha) of
              true -> 
                case maps:find(Alpha, S) of
                  {ok, NewAlpha} -> {ok, NewAlpha};
                  error -> {ok, Alpha}
                end;
              false -> error
            end;
            _ -> error
            end
          end,
          SubstitutedTypeVars = utils:everything(CollectFun, Tau),
          sets:union(Acc, sets:from_list(SubstitutedTypeVars, [{version, 2}]))
        end,
        sets:new([{version, 2}]),
        Maters),
    ?LOG_DEBUG("TypeVarsInMaters: ~p", TypeVarsInMaters),

    % Step 3b): find all variables that have at least both positive and negative occurrences in
    % the subtyping constraints
    PosNegTyvars = sets:fold(
      fun({scsubty, _, T1, T2}, Acc) ->
        Tyvars1 = collect_pos_neg_tyvars(T1),
        Tyvars2 = collect_pos_neg_tyvars(T2),
        ?LOG_DEBUG("T1: ~s, PosNeg: ~p", pretty:render_ty(T1), Tyvars1),
        ?LOG_DEBUG("T2: ~s, PosNeg: ~p", pretty:render_ty(T2), Tyvars2),
        sets:union([Acc, Tyvars1, Tyvars2])
      end,
      sets:new([{version, 2}]),
      Constrs
    ),
    ?LOG_DEBUG("PosNegTyvars: ~p", PosNegTyvars),
    A = sets:union(TypeVarsInMaters, PosNegTyvars),
    ?LOG_DEBUG("A: ~p", A),

    % Step 3c): Get all frame variables from A
    X = sets:filter(fun(Var) -> is_framevar(Var) end, A),
    ?LOG_DEBUG("Frame variables in A: ~p", X),

    % Step 3d): Collect all type variables which are not fixed, in the domain of the substitution
    % or in A:  α = var(D)\(∆∪dom(σ0)∪A)
    CollectFun = fun(Var) -> case Var of
      {var, Alpha} -> 
        case is_typevar(Alpha) of
          true -> {ok, Alpha};
          false -> error
        end;
      _ -> error
      end
    end,
    Var_D = sets:fold(
      fun({scsubty, _, T1, T2}, Acc) ->
        sets:union(
          sets:from_list(utils:everything(CollectFun, T1) ++ utils:everything(CollectFun, T2), [{version, 2}]),
          Acc
        )
      end,
      sets:new([{version, 2}]),
      Constrs
    ),
    Dom_Sigma = sets:from_list(lists:filter(fun(Var) -> is_typevar(Var) end, maps:keys(S)), [{version, 2}]),
    ?LOG_DEBUG("Domain of Sigma: ~p", Dom_Sigma),
    Alpha = sets:subtract(Var_D, sets:union(Dom_Sigma, A)),
    ?LOG_DEBUG("Alpha: ~p", Alpha),

    % Step 3e): Create fresh alpha and X
    X_Subst = sets:fold(
      fun(Framevar, Acc) ->
        maps:put(Framevar, fresh_typevar_name(Ctx), Acc)
      end,
      #{},
      X
    ),
    ?LOG_DEBUG("Got X Substs: ~p", X_Subst),
    Alpha_Subst = sets:fold(
      fun(Typevar, Acc) ->
        maps:put(Typevar, fresh_framevar_name(Ctx), Acc)
      end,
      #{},
      Alpha
    ),
    ?LOG_DEBUG("Got Alpha Substs: ~p", Alpha_Subst),

    % Step 3a): build sigma2
    Sigma2 = maps:merge(X_Subst, Alpha_Subst),

    % compose sigma2 and sigma
    Composition = compose({tally_subst, S, Fixed}, Sigma2),
    ?LOG_DEBUG("Got Composition: ~p", Composition),
    Composition.



-spec collect_pos_neg_tyvars(ast:ty()) -> sets:set(ast:ty_varname()).
collect_pos_neg_tyvars(Ty) -> 
  {Pos, Neg} = collect_pos_neg_tyvars(Ty, 0),
  ?LOG_DEBUG("Pos: ~p, Neg: ~p", Pos, Neg),  
  Res = sets:intersection(sets:from_list(Pos, [{version, 2}]), sets:from_list(Neg, [{version, 2}])),
  ?LOG_DEBUG("Pos & Neg: ~p", Res),
  Res.

-spec collect_pos_neg_tyvars(ast:ty(), non_neg_integer()) -> {[ast:ty_varname()], [ast:ty_varname()]}.
collect_pos_neg_tyvars({var, Alpha}, NegCount) ->
    case NegCount rem 2 of
        0 -> {[Alpha], []};
        1 -> {[], [Alpha]}
    end;

collect_pos_neg_tyvars({union, Types}, NegCount) ->
    lists:foldl(
      fun(T, {Evens, Odds}) ->
              {E2, O2} = collect_pos_neg_tyvars(T, NegCount),
              {Evens ++ E2, Odds ++ O2}
      end,
      {[], []},
      Types
    );

collect_pos_neg_tyvars({intersection, Types}, NegCount) ->
    lists:foldl(
      fun(T, {Evens, Odds}) ->
              {E2, O2} = collect_pos_neg_tyvars(T, NegCount),
              {Evens ++ E2, Odds ++ O2}
      end,
      {[], []},
      Types
    );

collect_pos_neg_tyvars({fun_full, ArgTypes, RetType}, NegCount) ->
    {EArgs, OArgs} = fold_types(ArgTypes, NegCount),
    {ERet, ORet} = collect_pos_neg_tyvars(RetType, NegCount),
    {EArgs ++ ERet, OArgs ++ ORet};

collect_pos_neg_tyvars({negation, Ty}, NegCount) ->
    collect_pos_neg_tyvars(Ty, NegCount + 1);

% Fallback
collect_pos_neg_tyvars(_, _) ->
    {[], []}.
    
% Helper to fold over a list of subtypes
-spec fold_types([ast:ty()], non_neg_integer()) -> {[ast:ty_varname()], [ast:ty_varname()]}.
fold_types(Types, NegCount) ->
    lists:foldl(
      fun(T, {Evens, Odds}) ->
              {E2, O2} = collect_pos_neg_tyvars(T, NegCount),
              {Evens ++ E2, Odds ++ O2}
      end,
      {[], []},
      Types
    ).

-spec compose([subst:t()], #{ast:ty_varname() => ast:ty_varname()}) -> [subst:t()].
compose({tally_subst, S, Fixed}, Sigma2) ->
        S1 = apply_subst(S, Sigma2),
        {tally_subst, S1, sets:union(Fixed, sets:from_list(maps:values(Sigma2), [{version, 2}]))}.

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
                {ok, NewName} -> 
                  case is_framevar(NewName) of
                    true -> {predef, dynamic}; % replace frame variables with dynamic (discrimination)
                    false -> {var, NewName} % keep as type variable
                  end;
                error -> case is_framevar(Name) of
                    true -> {predef, dynamic}; % replace frame variables with dynamic (discrimination)
                    false -> Ty % keep as type variable
                  end
            end;
        {union, Args} -> {union, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args)};
        {intersection, Args} -> {intersection, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args)};
        {fun_full, Args, RetTy} -> {fun_full, lists:map(fun(T) -> subst_ty(T, VarSubst) end, Args), subst_ty(RetTy, VarSubst)};
        _ -> Ty
    end.

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
