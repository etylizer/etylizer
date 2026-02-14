-module(constr_simp).

-include("log.hrl").

-export([
    simp_constrs/2,
    new_ctx/3,
    sanity_check/2
]).

-export_type([
    ctx/0
]).

-record(ctx,
        { symtab :: symtab:t(),
          env :: constr:constr_poly_env(),
          tyvar_counter :: counters:counters_ref(),
          sanity :: t:opt(ast_check:ty_map())
        }).
-type ctx() :: #ctx{}.

-spec new_ctx(symtab:t(),
             constr:constr_poly_env(),
             t:opt(ast_check:ty_map())) -> ctx().
new_ctx(Tab, Env, Sanity) ->
    Counter = counters:new(1, []),
    Ctx = #ctx{ tyvar_counter = Counter, env = Env, symtab = Tab, sanity = Sanity },
    Ctx.

-spec simp_constrs(ctx(), constr:constrs()) -> constr:simp_constrs().
simp_constrs(Ctx, Cs) ->
    sets:union(lists:map(fun (C) -> simp_constr(Ctx, C) end, sets:to_list(Cs))).

-spec lookup_var_ty(ctx(), ast:any_ref(), constr:locs(), string()) -> ast:ty_scheme().
lookup_var_ty(Ctx, X, Locs, Context) ->
    case maps:find(X, Ctx#ctx.env) of
        {ok, U} -> U;
        error ->
            case X of
                {local_ref, Y} ->
                    errors:bug("Unbound variable in " ++ Context ++ " ~w: ~p",
                         [Y, Ctx#ctx.env]);
                GlobalX ->
                    symtab:lookup_fun(GlobalX, loc(Locs), Ctx#ctx.symtab)
            end
    end.

-spec simp_cvar(ctx(), constr:locs(), ast:any_ref(), ast:ty()) -> constr:simp_constrs().
simp_cvar(Ctx, Locs, X, T) ->
    PolyTy = lookup_var_ty(Ctx, X, Locs, "constraint simplification"),
    utils:single({scsubty, loc(Locs), fresh_ty_scheme(Ctx, PolyTy), T}).

-spec simp_cvarmater(ctx(), constr:locs(), ast:any_ref(), ast:ty_varname()) -> constr:simp_constrs().
simp_cvarmater(Ctx, Locs, X, Alpha) ->
    PolyTy = lookup_var_ty(Ctx, X, Locs, "materialization constraint simplification"),
    Loc = loc(Locs),
    sets:from_list([{scmater, Loc, fresh_ty_scheme(Ctx, PolyTy), Alpha}]).

-spec simp_cop(ctx(), constr:locs(), atom(), arity(), ast:ty()) -> constr:simp_constrs().
simp_cop(Ctx, Locs, OpName, OpArity, T) ->
    PolyTy = symtab:lookup_op(OpName, OpArity, loc(Locs), Ctx#ctx.symtab),
    utils:single({scsubty, loc(Locs), fresh_ty_scheme(Ctx, PolyTy), T}).

-spec simp_cdef(ctx(), constr:constr_env(), constr:constrs()) -> constr:simp_constrs().
simp_cdef(Ctx, Env, Cs) ->
    NewCtx = extend_env(Ctx, Env),
    simp_constrs(NewCtx, Cs).

-spec simp_ccase(ctx(), constr:locs(), constr:constrs(), constr:constrs(), [constr:constr_case_branch()]) -> constr:simp_constrs().
simp_ccase(Ctx, Locs, CsScrut, CsExhaust, Bodies) ->
    case Ctx#ctx.sanity of
        {ok, TyMap0} -> constr_gen:sanity_check(CsScrut, TyMap0);
        error -> ok
    end,
    DsScrut = simp_constrs(Ctx, CsScrut),
    LocsScrut = loc(CsScrut),
    DsExhaust = simp_constrs(Ctx, CsExhaust),
    L = lists:map(fun (Body) -> simp_case_branch(Ctx, Body) end, Bodies),
    utils:single({sccase, {LocsScrut, DsScrut}, {loc(Locs), DsExhaust}, L}).

-spec simp_constr(ctx(), constr:constr()) -> constr:simp_constrs().
simp_constr(Ctx, C) ->
    ?LOG_TRACE("simp_constr, C=~w", C),
    case C of
        {csubty, Locs, T1, T2} ->
            utils:single({scsubty, loc(Locs), T1, T2});
        {cvar, Locs, X, T} ->
            simp_cvar(Ctx, Locs, X, T);
        {cvarmater, Locs, X, Alpha} ->
            simp_cvarmater(Ctx, Locs, X, Alpha);
        {cop, Locs, OpName, OpArity, T} ->
            simp_cop(Ctx, Locs, OpName, OpArity, T);
        {cdef, _Locs, Env, Cs} ->
            simp_cdef(Ctx, Env, Cs);
        {ccase, Locs, CsScrut, CsExhaust, Bodies} ->
            simp_ccase(Ctx, Locs, CsScrut, CsExhaust, Bodies)
    end.

-spec simp_case_branch(ctx(), constr:constr_case_branch()) -> constr:simp_constr_case_branch().
simp_case_branch(Ctx, {ccase_branch, BranchLocs, Payload}) ->
    {GuardsGammaI, GuardCsI} = constr:case_branch_guard(Payload),
    {BodyGammaI, BodyCsI} = constr:case_branch_body(Payload),
    ReduCsOrNone = constr:case_branch_bodyCond(Payload),
    LocBranch = loc(BranchLocs),
    ReduDs =
        case ReduCsOrNone of
            none -> none;
            ReduCs -> {LocBranch, simp_constrs(Ctx, ReduCs)}
        end,
    NewGuardsCtx = inter_env(Ctx, GuardsGammaI),
    GuardsDs = simp_constrs(NewGuardsCtx, GuardCsI),
    GuardsLoc = loc(GuardCsI, ast:loc_auto()), % GuardCsI can be empty
    NewBodyCtx = inter_env(Ctx, BodyGammaI),
    ResultCs = constr:case_branch_result(Payload),
    BodyDs = simp_constrs(NewBodyCtx, BodyCsI),
    BodyLoc = loc(BodyCsI),
    ResultDs = simp_constrs(NewBodyCtx, ResultCs),
    {sccase_branch, {GuardsLoc, GuardsDs}, ReduDs, {BodyLoc, BodyDs}, {LocBranch, ResultDs}}.

-spec inter_env(ctx(), constr:constr_env()) -> ctx().
inter_env(Ctx, Env) ->
    PolyEnv =
        maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    Combiner =
        fun (_Key, {ty_scheme, [], OldTy}, {ty_scheme, [], NewTy}) ->
            {ty_scheme, [], stdtypes:tinter(OldTy, NewTy)};
            (_Key, OldTy, NewTy) ->
                ?ABORT("BUG: inter_env, cannot combine polymorphic types ~s and ~s",
                    pretty:render_tyscheme(OldTy), pretty:render_tyscheme(NewTy))
        end,
    NewEnv = maps:merge_with(Combiner, Ctx#ctx.env, PolyEnv), % values from the second parameter have precedence
    ?LOG_TRACE("inter_env(~s, ~s) = ~s",
        pretty:render_poly_env(Ctx#ctx.env),
        pretty:render_mono_env(Env),
        pretty:render_poly_env(NewEnv)),
    Ctx#ctx { env = NewEnv }.

-spec fresh_tyvar(ctx(), ast:ty_varname()) -> ast:ty_varname().
fresh_tyvar(Ctx, Base) ->
    I = counters:get(Ctx#ctx.tyvar_counter, 1),
    counters:add(Ctx#ctx.tyvar_counter, 1, 1),
    S = utils:sformat("~w@~w", Base, I),
    list_to_atom(S).

-spec fresh_ty_scheme(ctx(), ast:ty_scheme()) -> ast:ty().
fresh_ty_scheme(_Ctx, {ty_scheme, [], T}) -> T;
fresh_ty_scheme(Ctx, {ty_scheme, Tyvars, T}) ->
    L =
        lists:map(
          fun({Alpha, Bound}) ->
                  Fresh = fresh_tyvar(Ctx, Alpha),
                  {Alpha, {intersection, [{var, Fresh}, Bound]}}
          end,
          Tyvars
         ),
    Subst = subst:from_list(L),
    subst:apply(Subst, T, {clean, Ctx#ctx.symtab}).

-spec loc(constr:locs() | sets:set(ast:loc()) | constr:constrs()) -> ast:loc().
loc(Locs) ->
    case loc(Locs, error) of
        error -> errors:bug("empty set of locations");
        X -> X
    end.

-spec loc(constr:locs() | sets:set(ast:loc()) | constr:constrs(), T) -> T | ast:loc().
loc({_, Locs}, Def) -> loc(Locs, Def);
loc(Set, Def) ->
    GetLoc = fun(X) ->
        % X is either a constr:constr() or a ast:loc()
        case X of
            {loc, _, _, _} -> X;
            _ -> loc(constr:locs_of_constr(X))
        end
    end,
    case sets:to_list(Set) of
        [First | Rest] ->
            lists:foldl(fun(X, L) -> ast:min_loc(L, GetLoc(X)) end, GetLoc(First), Rest);
        [] -> Def
    end.

-spec extend_env(ctx(), constr:constr_env()) -> ctx().
extend_env(Ctx, Env) ->
    PolyEnv =
        maps:map(fun(_Key, T) -> {ty_scheme, [], T} end, Env),
    NewEnv = maps:merge(Ctx#ctx.env, PolyEnv), % values from the second parameter have precedence
    ?LOG_TRACE("extend_env(~s, ~s) = ~s",
        pretty:render_poly_env(Ctx#ctx.env),
        pretty:render_mono_env(Env),
        pretty:render_poly_env(NewEnv)),
    Ctx#ctx { env = NewEnv }.

-spec sanity_check_one(constr:simp_constr(), ast_check:ty_map()) -> ok.
sanity_check_one(D, Spec) ->
    case ast_check:check_against_type(Spec, constr, simp_constr, D) of
        true ->
            ?LOG_DEBUG("Sanity check OK");
        false ->
            ?ABORT("Invalid simple constraint generated: ~w", D)
    end.

-spec sanity_check(constr:simp_constrs(), ast_check:ty_map()) -> ok.
sanity_check(Ds, Spec) ->
    lists:foreach(
        fun(D) -> sanity_check_one(D, Spec) end,
        sets:to_list(Ds)).
