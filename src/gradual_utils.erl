-module(gradual_utils).

-include("log.hrl").

-export([
    preprocess_constrs/2,
    postprocess/5,
    subst_ty/3
]).

-ifdef(TEST).
-export([
  collect_pos_neg_tyvars/2,
  replace_dynamic/2
]).
-endif.

-spec fresh_typevar_name(non_neg_integer()) -> {ast:ty_varname(), non_neg_integer()}.
fresh_typevar_name(Counter) ->
    NewId = Counter + 1,
    S = utils:sformat("$post_%~w", NewId),
    {list_to_atom(S), NewId}.

-spec fresh_typevar(non_neg_integer()) -> {ast:ty_var(), non_neg_integer()}.
fresh_typevar(Counter) ->
    {Name, C1} = fresh_typevar_name(Counter),
    {{var, Name}, C1}.

-spec fresh_framevar_name(non_neg_integer()) -> {ast:ty_varname(), non_neg_integer()}.
fresh_framevar_name(Counter) ->
    NewId = Counter + 1,
    S = utils:sformat("%~w", NewId),
    {list_to_atom(S), NewId}.

-spec fresh_framevar(non_neg_integer()) -> {ast:ty_var(), non_neg_integer()}.
fresh_framevar(Counter) ->
    {Name, C1} = fresh_framevar_name(Counter),
    {{var, Name}, C1}.


% When we see a gradual type with {predef, dynamic}
% we replace each dynamic with a fresh frame variable
-spec preprocess_constrs(constr:collected_constrs(), non_neg_integer()) ->
    {constr:subty_constrs(), constr:subty_constrs(), constr:mater_constrs(), subst:base_subst(), non_neg_integer()}.
preprocess_constrs(Constrs, Counter0) ->
    {SubtyConstrs, Maters, Counter1} = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Ms, C0}) ->
              {T1b, C1} = replace_dynamic(T1, C0),
              {T2b, C2} = replace_dynamic(T2, C1),
              {sets:add_element({scsubty, Loc, T1b, T2b}, Cs), Ms, C2};
            ({scmater, Loc, T1, T2}, {Cs, Ms, C0}) ->
              {T1b, C1} = replace_dynamic(T1, C0),
              {Cs, sets:add_element({scmater, Loc, T1b, T2}, Ms), C1};
            (Constr, {Cs, Ms, C0}) ->
              {sets:add_element(Constr, Cs), Ms, C0}
        end,
        {sets:new([{version,2}]), sets:new([{version,2}]), Counter0},
        Constrs),

    UnificationSubst = maps:from_list(lists:map(fun({scmater, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))),
    InlinedConstrs = sets:map(fun(Constr) ->
      case Constr of
        {scsubty, _Loc, T1, T2} -> {scsubty, _Loc, subst_ty(T1, UnificationSubst, no_discrimination), subst_ty(T2, UnificationSubst, no_discrimination)};
        Other -> Other
      end
    end, SubtyConstrs),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst, Counter1}.

-spec replace_dynamic(ast:ty(), non_neg_integer()) -> {ast:ty(), non_neg_integer()}.
replace_dynamic(Ty, Counter) ->
  utils:everywhere_acc(fun
    ({predef, dynamic}, C) ->
        {Var, C1} = fresh_framevar(C),
        {ok, Var, C1};
    (_, C) -> {error, C}
  end, Ty, Counter).

% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(subst:t(), constr:subty_constrs(), constr:subty_constrs(), symtab:t(), non_neg_integer()) ->
    {subst:t(), non_neg_integer()}.
postprocess({tally_subst, S, Fixed}, Constrs, Maters, SymTab, Counter0) ->
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
        Tyvars1 = collect_pos_neg_tyvars(T1, SymTab),
        Tyvars2 = collect_pos_neg_tyvars(T2, SymTab),
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
    {X_Subst, Counter1} = sets:fold(
      fun(Framevar, {Acc, C}) ->
        {FreshVar, C1} = fresh_typevar(C),
        {maps:put(Framevar, FreshVar, Acc), C1}
      end,
      {#{}, Counter0},
      X
    ),

    {Alpha_Subst, Counter2} = sets:fold(
      fun(Typevar, {Acc, C}) ->
        {FreshVar, C1} = fresh_framevar(C),
        {maps:put(Typevar, FreshVar, Acc), C1}
      end,
      {#{}, Counter1},
      Alpha
    ),

    % Step 3a): build sigma2
    Sigma2 = maps:merge(X_Subst, Alpha_Subst),

    % compose sigma2 and sigma
    Composition = compose({tally_subst, S, Fixed}, Sigma2),
    {Composition, Counter2}.

% Returns the set of variable names appearing in both positive and negative positions in Ty.
% Delegates to subst:collect_vars/6 for exhaustive AST traversal.
-spec collect_pos_neg_tyvars(ast:ty(), symtab:t()) -> sets:set(ast:ty_varname()).
collect_pos_neg_tyvars(Ty, SymTab) ->
    VarPositions = subst:collect_vars(Ty, 0, #{}, sets:new(), SymTab, #{}),
    maps:fold(
      fun(Name, Positions, Acc) ->
          case lists:usort(Positions) of
              [0, 1] -> sets:add_element(Name, Acc);
              _ -> Acc
          end
      end,
      sets:new([{version, 2}]),
      VarPositions).

-spec compose(subst:t(), subst:base_subst()) -> subst:t().
compose({tally_subst, S, Fixed}, Sigma2) ->
        S1 = apply_subst(S, Sigma2),
        {tally_subst, S1, sets:union(Fixed, sets:from_list(maps:values(Sigma2), [{version, 2}]))}.

-spec apply_subst(subst:base_subst(), subst:base_subst()) -> subst:base_subst().
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
    ({var, Name}) when is_atom(Name) ->
      NewTy = find_in_subst({var, Name}, VarSubst),
      case Mode of
        discriminate -> {ok, utils:everywhere(fun
          ({var, N}) when is_atom(N) ->
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

-spec collect_tyvars(ast:ty()) -> [ast:ty_varname()].
collect_tyvars(Ty) ->
    utils:everything(
      fun
        ({var, Name}) when is_atom(Name) ->
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