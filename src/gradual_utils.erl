-module(gradual_utils).

-include("log.hrl").

-export([
    init/0,
    clean/0,
    preprocess_constrs/1,
    postprocess/3,
    subst_ty/3
]).

-ifdef(TEST).
-export([
  collect_pos_neg_tyvars/1,
  replace_dynamic/1
]).
-endif.

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

-spec fresh_typevar() -> ast:ty_var().
fresh_typevar() ->
    X = fresh_typevar_name(),
    {var, X}.

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
-spec preprocess_constrs(constr:subty_constrs()) -> {constr:subty_constrs(), constr:subty_constrs(), constr:mater_constrs(), subst:base_subst()}.
preprocess_constrs(Constrs) ->
    {SubtyConstrs, Maters} = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Maters}) ->
              {sets:add_element({scsubty, Loc, replace_dynamic(T1), replace_dynamic(T2)}, Cs), Maters};
            ({scmater, Loc, T1, T2}, {Cs, Maters}) ->
              {Cs, sets:add_element({scmater, Loc, replace_dynamic(T1), T2}, Maters)};
            (Constr, {Cs, Maters}) ->
              {sets:add_element(Constr, Cs), Maters}
        end,
        {sets:new([{version,2}]), sets:new([{version,2}])},
        Constrs),
    
    UnificationSubst = maps:from_list(lists:map(fun({scmater, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))),
    InlinedConstrs = sets:map(fun(Constr) -> 
      case Constr of
        {scsubty, _Loc, T1, T2} -> {scsubty, _Loc, subst_ty(T1, UnificationSubst, no_discrimination), subst_ty(T2, UnificationSubst, no_discrimination)};
        Other -> Other
      end
    end, SubtyConstrs),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst}.

-spec replace_dynamic(ast:ty()) -> ast:ty().
replace_dynamic(Ty) -> 
  utils:everywhere(fun
    ({predef, dynamic}) -> {ok, fresh_framevar()};
    (_) -> error
  end, Ty).

% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(subst:t(), constr:subty_constrs(), constr:subty_constrs()) -> subst:t().
postprocess({tally_subst, S, Fixed}, Constrs, Maters) ->
    ?LOG_DEBUG("Postprocessing tally substitution:~nSubstitution:~n~s~nConstraints:~n~s~nMaterialization constraints:~n~s",
        pretty:render_subst(S),
        pretty:render_constr(Constrs),
        pretty:render_constr(Maters)),
    % Step 3b): find all type variables appearing in the gradual types in materialization constraints
    % and substitute them with the found tally solution 
    TypeVarsInMaters = sets:fold(
        fun({scmater, _, Tau, _}, Acc) ->
          TypeVars = collect_tyvars(Tau),
          sets:union(Acc, sets:from_list(TypeVars, [{version, 2}]))
        end,
        sets:new([{version, 2}]),
        Maters),
    TypeVarsInSubsts = sets:fold(
      fun(Alpha, Acc) ->
        case maps:find(Alpha, S) of
          {ok, Ty} ->
            TypeVars = collect_tyvars(Ty),
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
    Var_D = sets:fold(
      fun({scsubty, _, T1, T2}, Acc) ->
        sets:union(
          sets:from_list(collect_tyvars(T1) ++ collect_tyvars(T2), [{version, 2}]),
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
        maps:put(Framevar, fresh_typevar(), Acc)
      end,
      #{},
      X
    ),

    Alpha_Subst = sets:fold(
      fun(Typevar, Acc) ->
        maps:put(Typevar, fresh_framevar(), Acc)
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
    fold_types(Types, NegCount);

collect_pos_neg_tyvars({intersection, Types}, NegCount) ->
    fold_types(Types, NegCount);

collect_pos_neg_tyvars({tuple, Types}, NegCount) ->
    fold_types(Types, NegCount);

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

-spec compose([subst:t()], subst:base_subst()) -> [subst:t()].
compose({tally_subst, S, Fixed}, Sigma2) ->
        S1 = apply_subst(S, Sigma2),
        {tally_subst, S1, sets:union(Fixed, sets:from_list(maps:values(Sigma2), [{version, 2}]))}.

-spec apply_subst(subst:t(), subst:base_subst()) -> subst:t().
apply_subst(S, Sigma2) ->
    maps:fold(
        fun(Var, Ty, Acc) ->
            case is_framevar(Var) of
              true -> maps:remove(Var, Acc); % frame variables are removed from the substitution
              false -> maps:put(Var, subst_ty(Ty, Sigma2, discriminate), Acc)
            end
        end,
        S,
        S).

-spec subst_ty(ast:ty(), subst:base_subst(), atom()) -> ast:ty().
subst_ty(Ty, VarSubst, Mode) -> 
  utils:everywhere(fun
    ({var, Name}) ->
      NewTy = find_in_subst({var, Name}, VarSubst),
      case Mode of
        discriminate -> {ok, utils:everywhere(fun
          ({var, N}) ->
            case is_framevar(N) of
              true -> {ok, {predef, dynamic}}; % replace frame variables with dynamic (discrimination)
              false -> error % keep as type variable
            end;
          (_) -> error
        end, NewTy)};
        _ -> {ok, NewTy}
      end;
    (_) -> error
  end, Ty).

-spec find_in_subst(ast:ty_var(), subst:base_subst()) -> ast:ty().
find_in_subst({var, Name}, VarSubst) ->
    case maps:find(Name, VarSubst) of
        {ok, SubstTy} -> SubstTy;
        error -> {var, Name}
    end.

-spec collect_tyvars(ast:ty()) -> sets:set(ast:ty_varname()).
collect_tyvars(Ty) ->
    utils:everything(
      fun
        ({var, Name}) -> 
          case is_typevar(Name) of
            true -> {ok, Name};
            false -> error
          end;
        (_) -> error
      end,
      Ty
    ).

-spec is_framevar
  (ast:ty_varname()) -> boolean();
  (ast:ty_var()) -> boolean().
is_framevar(Name) when is_atom(Name) -> starts_with(Name, "%");
is_framevar({var, Name}) -> starts_with(Name, "%");
is_framevar(_) -> false.

-spec is_typevar(ast:ty_varname()) -> boolean().
is_typevar(Name) -> starts_with(Name, "$").

-spec starts_with(ast:ty_varname(), string()) -> boolean().
starts_with(Name, Prefix) ->
    case string:prefix(atom_to_list(Name), Prefix) of
        nomatch -> false;
        _ -> true
    end.