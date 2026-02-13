-module(gradual_utils).

-include("log.hrl").

-record(ctx, { var_counter :: counters:counters_ref() }).
-type ctx() :: #ctx{}.
-export_type([ctx/0]).

-export([
    new_ctx/0,
    preprocess_constrs/2,
    postprocess/4
]).

-ifdef(TEST).
-export([
  collect_pos_neg_tyvars/2,
  compose/2,
  discriminate_framevars/1,
  replace_dynamic/2
]).
-endif.

-spec new_ctx() -> ctx().
new_ctx() -> #ctx{ var_counter = counters:new(1, []) }.

-spec fresh_typevar_name(ctx()) -> ast:ty_varname().
fresh_typevar_name(Ctx) ->
    counters:add(Ctx#ctx.var_counter, 1, 1),
    NewId = counters:get(Ctx#ctx.var_counter, 1),
    S = utils:sformat("$post_%~w", NewId),
    list_to_atom(S).

-spec fresh_typevar(ctx()) -> ast:ty_var().
fresh_typevar(Ctx) ->
    Name = fresh_typevar_name(Ctx),
    {var, Name}.

-spec fresh_framevar_name(ctx()) -> ast:ty_varname().
fresh_framevar_name(Ctx) ->
    counters:add(Ctx#ctx.var_counter, 1, 1),
    NewId = counters:get(Ctx#ctx.var_counter, 1),
    S = utils:sformat("%~w", NewId),
    list_to_atom(S).

-spec fresh_framevar(ctx()) -> ast:ty_var().
fresh_framevar(Ctx) ->
    Name = fresh_framevar_name(Ctx),
    {var, Name}.


% When we see a gradual type with {predef, dynamic}
% we replace each dynamic with a fresh frame variable
-spec preprocess_constrs(constr:collected_constrs(), ctx()) ->
    {constr:subty_constrs(), constr:subty_constrs(), constr:mater_constrs(), subst:base_subst()}.
preprocess_constrs(Constrs, Ctx) ->
    {SubtyConstrs, Maters} = sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Ms}) ->
              T1b = replace_dynamic(T1, Ctx),
              T2b = replace_dynamic(T2, Ctx),
              {sets:add_element({scsubty, Loc, T1b, T2b}, Cs), Ms};
            ({scmater, Loc, T1, T2}, {Cs, Ms}) ->
              T1b = replace_dynamic(T1, Ctx),
              {Cs, sets:add_element({scmater, Loc, T1b, T2}, Ms)};
            (Constr, {Cs, Ms}) ->
              {sets:add_element(Constr, Cs), Ms}
        end,
        {sets:new(), sets:new()},
        Constrs),

    UnificationSubst = maps:from_list(lists:map(fun({scmater, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))),
    InlinedConstrs = sets:map(fun(Constr) ->
      case Constr of
        {scsubty, _Loc, T1, T2} -> {scsubty, _Loc, subst:apply_base(UnificationSubst, T1), subst:apply_base(UnificationSubst, T2)};
        Other -> Other
      end
    end, SubtyConstrs),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst}.

-spec replace_dynamic(ast:ty(), ctx()) -> ast:ty().
replace_dynamic(Ty, Ctx) ->
  utils:everywhere(fun
    ({predef, dynamic}) -> {ok, fresh_framevar(Ctx)};
    (_) -> error
  end, Ty).

% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(subst:t(), constr:subty_constrs(), constr:subty_constrs(), symtab:t()) ->
    subst:t().
postprocess({tally_subst, S, Fixed}, Constrs, Maters, SymTab) ->
    ?LOG_DEBUG("Postprocessing tally substitution:~nSubstitution:~n~s~nConstraints:~n~s~nMaterialization constraints:~n~s",
        pretty:render_subst(S),
        pretty:render_constr(Constrs),
        pretty:render_constr(Maters)),
    Ctx = new_ctx(),
    % Step 3b): find all type variables appearing in the gradual types in materialization constraints
    % and substitute them with the found tally solution
    TypeVarsInMaters = sets:fold(
        fun({scmater, _, Tau, _}, Acc) ->
          TypeVars = collect_tyvars(Tau),
          sets:union(Acc, sets:from_list(TypeVars))
        end,
        sets:new(),
        Maters),
    TypeVarsInSubsts = sets:fold(
      fun(Alpha, Acc) ->
        case maps:find(Alpha, S) of
          {ok, Ty} ->
            TypeVars = collect_tyvars(Ty),
            sets:union(Acc, sets:from_list(TypeVars));
          error -> Acc
        end
      end,
      sets:new(),
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
      sets:new(),
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
          sets:from_list(collect_tyvars(T1) ++ collect_tyvars(T2)),
          Acc
        )
      end,
      sets:new(),
      Constrs
    ),
    Dom_Sigma = sets:from_list(lists:filter(fun(Var) -> is_typevar(Var) end, maps:keys(S))),
    Alpha = sets:subtract(Var_D, sets:union(Dom_Sigma, A)),

    % Step 3e): Create fresh alpha and X
    X_Subst = sets:fold(
      fun(Framevar, Acc) ->
        FreshVar = fresh_typevar(Ctx),
        maps:put(Framevar, FreshVar, Acc)
      end,
      #{},
      X
    ),

    Alpha_Subst = sets:fold(
      fun(Typevar, Acc) ->
        FreshVar = fresh_framevar(Ctx),
        maps:put(Typevar, FreshVar, Acc)
      end,
      #{},
      Alpha
    ),

    % Step 3a): build sigma2
    Sigma2 = maps:merge(X_Subst, Alpha_Subst),

    % compose sigma2 and sigma
    compose({tally_subst, S, Fixed}, Sigma2).

% Returns the set of variable names appearing in both positive and negative positions in Ty.
% Delegates to subst:collect_vars/4 for exhaustive AST traversal.
-spec collect_pos_neg_tyvars(ast:ty(), symtab:t()) -> sets:set(ast:ty_varname()).
collect_pos_neg_tyvars(Ty, SymTab) ->
    UnfoldedTy = ast_utils:unfold_ty(SymTab, Ty),
    VarPositions = subst:collect_vars(UnfoldedTy, 0, #{}, sets:new()),
    maps:fold(
      fun(Name, Positions, Acc) ->
          case lists:usort(Positions) of
              [0, 1] -> sets:add_element(Name, Acc);
              _ -> Acc
          end
      end,
      sets:new(),
      VarPositions).

-spec compose(subst:t(), subst:base_subst()) -> subst:t().
compose({tally_subst, S, Fixed}, Sigma2) ->
        S1 = apply_subst(S, Sigma2),
        {tally_subst, S1, sets:union(Fixed, sets:from_list([N || {var, N} <- maps:values(Sigma2)]))}.

-spec apply_subst(subst:base_subst(), subst:base_subst()) -> subst:base_subst().
apply_subst(S, Sigma2) ->
    maps:fold(
        fun(Var, Ty, Acc) ->
            case is_framevar(Var) of
              true -> maps:remove(Var, Acc); % frame variables are removed from the substitution
              false -> maps:put(Var, discriminate_framevars(subst:apply_base(Sigma2, Ty)), Acc)
            end
        end,
        S,
        S).

-spec discriminate_framevars(ast:ty()) -> ast:ty().
discriminate_framevars(Ty) ->
    utils:everywhere(fun
        ({var, N}) when is_atom(N) ->
            case is_framevar(N) of
                true -> {ok, {predef, dynamic}};
                false -> error
            end;
        (_) -> error
    end, Ty).

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
