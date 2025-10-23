-module(gradual_utils).

-export([
    init/0,
    clean/0,
    preprocess_constrs/1,
    postprocess/3
]).

-define(VAR_ETS, framevariable_counter_ets_table).
-define(ALL_ETS, [?VAR_ETS]).


-spec init() -> _.
init() ->
  case ets:whereis(?VAR_ETS) of
      undefined -> 
        [ets:new(T, [public, set, named_table]) || T <- ?ALL_ETS],
        ets:insert(?VAR_ETS, {variable_id, 0});
      _ -> ok
  end.

-spec clean() -> _.
clean() ->
  case ets:whereis(?VAR_ETS) of
      undefined -> ok;
      _ -> 
        [ets:delete(T) || T <- ?ALL_ETS]
  end.


-spec fresh_typevar_name() -> ast:ty_varname().
fresh_typevar_name() ->
    NewId = ets:update_counter(?VAR_ETS, variable_id, {2,1}),
    S = utils:sformat("$post_%~w", NewId),
    list_to_atom(S).

-spec fresh_framevar_name() -> ast:ty_varname().
fresh_framevar_name() ->
    NewId = ets:update_counter(?VAR_ETS, variable_id, {2,1}),
    S = utils:sformat("%~w", NewId),
    list_to_atom(S).

-spec fresh_framevar() -> ast:ty_var().
fresh_framevar() ->
    X = fresh_framevar_name(),
    {var, X}.


% When we see a gradual type with {predef, dynamic}
% we replace each dynamic with a fresh frame variable
-spec preprocess_constrs(constr:subty_constrs()) -> {constr:subty_constrs(), constr:subty_constrs()}.
preprocess_constrs(Constrs) ->
    {SubtyConstrs, Maters} = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Maters}) ->
              {sets:add_element({scsubty, Loc, replace_dynamic(T1), replace_dynamic(T2)}, Cs), Maters};
            ({scmater, Loc, T1, T2}, {Cs, Maters}) ->
              {Cs, sets:add_element({scmater, Loc, replace_dynamic(T1), {var, T2}}, Maters)};
            (Constr, {Cs, Maters}) ->
              {sets:add_element(Constr, Cs), Maters}
        end,
        {sets:new([{version,2}]), sets:new([{version,2}])},
        Constrs),
    
    UnificationSubsts = maps:from_list(lists:map(fun({scmater, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))),
    InlinedConstrs = sets:map(fun(Constr) -> 
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
    end, SubtyConstrs),
    {InlinedConstrs, SubtyConstrs, Maters}.

-spec replace_dynamic(ast:ty()) -> ast:ty().
replace_dynamic({predef, dynamic}) -> fresh_framevar();
replace_dynamic({var, Name}) -> {var, Name};
replace_dynamic({union, Types}) -> {union, lists:map(fun(T) -> replace_dynamic(T) end, Types)};
replace_dynamic({intersection, Types}) -> {intersection, lists:map(fun(T) -> replace_dynamic(T) end, Types)};
replace_dynamic({fun_full, ArgTypes, RetType}) ->
    {fun_full, lists:map(fun(T) -> replace_dynamic(T) end, ArgTypes), replace_dynamic(RetType)};
replace_dynamic({list, Ty}) -> {list, replace_dynamic(Ty)};
replace_dynamic(Ty) -> Ty.

% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(subst:t(), constr:subty_constrs(), constr:subty_constrs()) -> subst:t().
postprocess({tally_subst, S, Fixed}, Constrs, Maters) ->
    % Step 3b): find all type variables appearing in the gradual types in materialization constraints
    % and substitute them with the found tally solution 
    TypeVarsInMaters = sets:fold(
        fun({scmater, _, Tau, _}, Acc) ->
          CollectFun = fun(X) -> case X of
            {var, Alpha} -> case is_typevar(Alpha) of
              true -> {ok, Alpha};
              false -> error
            end;
            _ -> error
            end
          end,
          TypeVars = utils:everything(CollectFun, Tau),
          sets:union(Acc, sets:from_list(TypeVars, [{version, 2}]))
        end,
        sets:new([{version, 2}]),
        Maters),
    TypeVarsInSubsts = sets:fold(
      fun(Alpha, Acc) ->
        case maps:find(Alpha, S) of
          {ok, Ty} ->
            CollectFun = fun(X) -> case X of
              {var, Beta} -> case is_typevar(Beta) of
                true -> {ok, Beta};
                false -> error
              end;
              _ -> error
              end
            end,
            TypeVars = utils:everything(CollectFun, Ty),
            sets:union(Acc, sets:from_list(TypeVars, [{version, 2}]));
          error -> Acc
        end
      end,
      sets:new([{version, 2}]),
      TypeVarsInMaters
    ),

    % Step 3b): find all variables that have at least both positive and negative occurrences in
    % the subtyping constraints
    PosNegTyvars = sets:fold(
      fun({scsubty, _, T1, T2}, Acc) ->
        Tyvars1 = collect_pos_neg_tyvars(T1),
        Tyvars2 = collect_pos_neg_tyvars(T2),
        sets:union([Acc, Tyvars1, Tyvars2])
      end,
      sets:new([{version, 2}]),
      Constrs
    ),
    A = sets:union(TypeVarsInSubsts, PosNegTyvars),

    % Step 3c): Get all frame variables from A
    X = sets:filter(fun(Var) -> is_framevar(Var) end, A),

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
    Alpha = sets:subtract(Var_D, sets:union(Dom_Sigma, A)),

    % Step 3e): Create fresh alpha and X
    X_Subst = sets:fold(
      fun(Framevar, Acc) ->
        maps:put(Framevar, fresh_typevar_name(), Acc)
      end,
      #{},
      X
    ),

    Alpha_Subst = sets:fold(
      fun(Typevar, Acc) ->
        maps:put(Typevar, fresh_framevar_name(), Acc)
      end,
      #{},
      Alpha
    ),

    % Step 3a): build sigma2
    Sigma2 = maps:merge(X_Subst, Alpha_Subst),

    % compose sigma2 and sigma
    Composition = compose({tally_subst, S, Fixed}, Sigma2),
    Composition.

-spec collect_pos_neg_tyvars(ast:ty()) -> sets:set(ast:ty_varname()).
collect_pos_neg_tyvars(Ty) -> 
  {Pos, Neg} = collect_pos_neg_tyvars(Ty, 0),  
  Res = sets:intersection(sets:from_list(Pos, [{version, 2}]), sets:from_list(Neg, [{version, 2}])),
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
            case is_framevar(Var) of
              true -> maps:remove(Var, Acc); % frame variables are removed from the substitution
              false -> maps:put(Var, subst_ty(Ty, Sigma2), Acc)
            end
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