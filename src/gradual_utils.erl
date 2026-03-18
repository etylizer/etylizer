-module(gradual_utils).

-include("log.hrl").

-record(ctx, { var_counter :: counters:counters_ref() }).
-type ctx() :: #ctx{}.
-export_type([ctx/0]).

-export([
    new_ctx/0,
    inline_materializations/1,
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
    {SubtyConstrs, Maters} = separate_constrs(Constrs, Ctx),
    UnificationSubst0 = build_unification_subst(Maters),
    % Compose the substitution to resolve chains (e.g. $0 -> T, $2 -> $0 /\ S)
    % into fully resolved mappings before inlining.
    UnificationSubst = compose_subst(UnificationSubst0),
    InlinedConstrs = inline_subst(UnificationSubst, SubtyConstrs),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst}.

% Inline materializations into collected constraints, removing scmater entries.
% Returns the inlined scsubty-only constraints and the composed substitution.
-spec inline_materializations(constr:collected_constrs()) ->
    {constr:collected_constrs(), subst:base_subst()}.
inline_materializations(Constrs) ->
    {SubtyConstrs, MaterConstrs} = sets:fold(
        fun ({scsubty, _, _, _} = C, {Ss, Ms}) -> {sets:add_element(C, Ss), Ms};
            ({scmater, _, _, _} = C, {Ss, Ms}) -> {Ss, sets:add_element(C, Ms)}
        end,
        {sets:new(), sets:new()},
        Constrs),
    MaterSubst = compose_subst(build_unification_subst(MaterConstrs)),
    Inlined = inline_subst(MaterSubst, SubtyConstrs),
    {Inlined, MaterSubst}.

% Separate collected constraints into subtyping and materialization constraints,
% replacing dynamic() with fresh frame variables.
-spec separate_constrs(constr:collected_constrs(), ctx()) ->
    {constr:subty_constrs(), constr:mater_constrs()}.
separate_constrs(Constrs, Ctx) ->
    sets:fold(
        fun
            ({scsubty, Loc, T1, T2}, {Cs, Ms}) ->
              T1b = replace_dynamic(T1, Ctx),
              T2b = replace_dynamic(T2, Ctx),
              {sets:add_element({scsubty, Loc, T1b, T2b}, Cs), Ms};
            ({scmater, Loc, T1, T2}, {Cs, Ms}) ->
              T1b = replace_dynamic(T1, Ctx),
              {Cs, sets:add_element({scmater, Loc, T1b, T2}, Ms)}
        end,
        {sets:new(), sets:new()},
        Constrs).

% Apply a substitution to its own values until fixed point, resolving chains.
% The materialization substitution is acyclic, so this always terminates.
-spec compose_subst(subst:base_subst()) -> subst:base_subst().
compose_subst(Subst) ->
    Composed = maps:map(fun(_V, Ty) -> subst:apply_base(Subst, Ty) end, Subst),
    case Composed =:= Subst of
        true -> Subst;
        false -> compose_subst(Composed)
    end.

% Build a unification substitution from materialization constraints.
-spec build_unification_subst(constr:mater_constrs()) -> subst:base_subst().
build_unification_subst(Maters) ->
    maps:from_list(lists:map(fun({scmater, _, Tau, Alpha}) -> {Alpha, Tau} end, sets:to_list(Maters))).

-spec inline_subst(subst:base_subst(), constr:subty_constrs()) -> constr:subty_constrs().
inline_subst(UnificationSubst, SubtyConstrs) ->
    sets:map(fun({scsubty, Loc, T1, T2}) ->
      {scsubty, Loc, subst:apply_base(UnificationSubst, T1), subst:apply_base(UnificationSubst, T2)}
    end, SubtyConstrs).

-spec replace_dynamic(ast:ty(), ctx()) -> ast:ty().
replace_dynamic(Ty, Ctx) ->
  utils:everywhere(fun
    ({predef, dynamic}) -> {ok, fresh_framevar(Ctx)};
    (_) -> error
  end, Ty).

% This postprocess step refers to the work of Petrucciani in his PhD thesis (chapter 10.4.2)
-spec postprocess(subst:tally_subst(), constr:subty_constrs(), constr:mater_constrs(), symtab:t()) ->
    subst:tally_subst().
postprocess({tally_subst, S, Fixed}, Constrs, Maters, SymTab) ->
    ?LOG_DEBUG("Postprocessing tally substitution:~nSubstitution:~n~s~nConstraints:~n~s~nMaterialization constraints:~n~s",
        pretty:render_subst(S),
        pretty:render_constr(Constrs),
        pretty:render_constr(Maters)),
    Ctx = new_ctx(),
    A = compute_A(S, Constrs, Maters, SymTab),

    % Step 3c): Get all frame variables from A
    X = sets:filter(fun(Var) -> is_framevar(Var) end, A),

    % Step 3d)
    Alpha = compute_alpha(S, Constrs, A),

    % Step 3e): Create fresh alpha and X
    Sigma2 = build_sigma2(X, Alpha, Ctx),

    % compose sigma2 and sigma
    compose({tally_subst, S, Fixed}, Sigma2).

-spec compute_A(subst:base_subst(), constr:subty_constrs(), constr:mater_constrs(), symtab:t()) ->
    sets:set(ast:ty_varname()).
compute_A(S, Constrs, Maters, SymTab) ->
    % Step 3b): find all type variables appearing in the gradual types in materialization constraints
    % and substitute them with the found tally solution
    TypeVarsInMaters = collect_mater_tyvars(Maters),
    TypeVarsInSubsts = collect_subst_tyvars(TypeVarsInMaters, S),
    % Step 3b): find all variables that have at least both positive and negative occurrences in
    % the subtyping constraints
    PosNegTyvars = collect_pos_neg_constrs_tyvars(Constrs, SymTab),
    sets:union(TypeVarsInSubsts, PosNegTyvars).

-spec collect_mater_tyvars(constr:mater_constrs()) -> sets:set(ast:ty_varname()).
collect_mater_tyvars(Maters) ->
    sets:fold(
        fun({scmater, _, Tau, _}, Acc) ->
          TypeVars = collect_tyvars(Tau),
          sets:union(Acc, sets:from_list(TypeVars))
        end,
        sets:new(),
        Maters).

-spec collect_subst_tyvars(sets:set(ast:ty_varname()), subst:base_subst()) -> sets:set(ast:ty_varname()).
collect_subst_tyvars(TypeVarsInMaters, S) ->
    sets:fold(
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
    ).

-spec collect_pos_neg_constrs_tyvars(constr:subty_constrs(), symtab:t()) -> sets:set(ast:ty_varname()).
collect_pos_neg_constrs_tyvars(Constrs, SymTab) ->
    sets:fold(
      fun({scsubty, _, T1, T2}, Acc) ->
        Tyvars1 = collect_pos_neg_tyvars(T1, SymTab),
        Tyvars2 = collect_pos_neg_tyvars(T2, SymTab),
        sets:union([Acc, Tyvars1, Tyvars2])
      end,
      sets:new(),
      Constrs
    ).

-spec compute_alpha(subst:base_subst(), constr:subty_constrs(), sets:set(ast:ty_varname())) ->
    sets:set(ast:ty_varname()).
compute_alpha(S, Constrs, A) ->
    % Collect all type variables which are not fixed, in the domain of the substitution
    % or in A:  a = var(D)\(D u dom(s0) u A)
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
    sets:subtract(Var_D, sets:union(Dom_Sigma, A)).

-spec build_sigma2(sets:set(ast:ty_varname()), sets:set(ast:ty_varname()), ctx()) -> subst:base_subst().
build_sigma2(X, Alpha, Ctx) ->
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
    maps:merge(X_Subst, Alpha_Subst).

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

-spec compose(subst:tally_subst(), subst:base_subst()) -> subst:tally_subst().
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
is_framevar({var, Name}) -> starts_with(Name, "%").

-spec is_typevar(ast:ty_varname()) -> boolean().
is_typevar(Name) -> starts_with(Name, "$").

-spec starts_with(ast:ty_varname(), string()) -> boolean().
starts_with(Name, Prefix) ->
    case string:prefix(atom_to_list(Name), Prefix) of
        nomatch -> false;
        _ -> true
    end.
