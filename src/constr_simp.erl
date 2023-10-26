-module(constr_simp).

-include_lib("log.hrl").

-export([
    simp_constrs/2,
    new_ctx/4,
    sanity_check/2
]).

-export_type([unmatched_branch_mode/0]).

-record(ctx,
        { symtab :: symtab:t(),
          env :: constr:constr_poly_env(),
          tyvar_counter :: counters:counters_ref(),
          sanity :: t:opt(ast_check:ty_map()),
          unmatched_branch :: unmatched_branch_mode()
        }).
-type ctx() :: #ctx{}.

% Mode ignore_branch specifies that branches of a case that cannot be matched
% are excluded while type-checking.

% Mode report should report an error in case a branch cannot be match.
%
% When type-checking a function against an intersection type, we use mode
% ignore_branch. Otherwise, we use report.
%
% Currently, it is not possible to check for unmatched branches when type-checking
% against an intersection type. Here, we could report an error if the same branch
% is excluded for every element of the intersection. But this is not implemented.
-type unmatched_branch_mode() :: ignore_branch | report.

-spec new_ctx(symtab:t(), constr:constr_poly_env(),
              t:opt(ast_check:ty_map()), unmatched_branch_mode()) -> ctx().
new_ctx(Tab, Env, Sanity, BranchMode) ->
    Counter = counters:new(1, []),
    Ctx = #ctx{ tyvar_counter = Counter, env = Env, symtab = Tab, sanity = Sanity,
                unmatched_branch = BranchMode },
    Ctx.

% The result of constraint simplication is either a single error or potentially several sets
% of subtyping constraints (there is at least one such set). A solution to any of these sets
% is a solution to the original constraint problem.
-type simp_constrs_result() ::
    {simp_constrs_ok, nonempty_list(constr:simp_constrs())} |
    {simp_constrs_error, {simp_constrs_error_kind(), ast:loc()}}.

-spec zero_simp_constrs_result() -> simp_constrs_result().
zero_simp_constrs_result() -> {simp_constrs_ok, [sets:new()]}.

-type simp_constrs_error_kind() :: tyerror | redundant_branch | non_exhaustive_case.

-spec is_simp_constrs_error(simp_constrs_result()) -> boolean().
is_simp_constrs_error({simp_constrs_error, _}) -> true;
is_simp_constrs_error(_) -> false.

-type simp_constrs_cont() :: fun((simp_constrs_result(), nonempty_list(constr:simp_constrs())) -> simp_constrs_result()).

-spec simp_constrs_if_ok(simp_constrs_result(), simp_constrs_cont()) -> simp_constrs_result().
simp_constrs_if_ok({simp_constrs_ok, L} = C, F) -> F(C, L);
simp_constrs_if_ok(X, _) -> X.

-spec cross_union(simp_constrs_result(), simp_constrs_result()) -> simp_constrs_result().
cross_union({simp_constrs_error, _} = Err, _) -> Err;
cross_union(_, {simp_constrs_error, _} = Err) -> Err;
cross_union({simp_constrs_ok, L1}, {simp_constrs_ok, L2}) ->
    ResultList = lists:flatmap(
      fun(S1) ->
              lists:map(fun(S2) -> sets:union(S1, S2) end, L2)
      end,
      L1),
    {simp_constrs_ok, ResultList}.

-spec simp_constrs(ctx(), constr:constrs()) -> simp_constrs_result().
simp_constrs(Ctx, Cs) ->
    ?LOG_TRACE("simp_constrs, Cs=~w", Cs),
    sets:fold(
      fun(C, Dss2) ->
        simp_constrs_if_ok(Dss2,
            fun(_, _) ->
                Dss1 = simp_constr(Ctx, C),
                case Ctx#ctx.sanity of
                    {ok, TyMap} -> sanity_check(Dss1, TyMap);
                    error -> ok
                end,
                cross_union(Dss1, Dss2)
            end)
      end,
      zero_simp_constrs_result(), Cs).

-spec simp_constr(ctx(), constr:constr()) -> simp_constrs_result().
simp_constr(Ctx, C) ->
    ?LOG_TRACE("simp_constr, C=~w", C),
    case C of
        {csubty, _, _, _} -> {simp_constrs_ok, [single(C)]};
        {cvar, Locs, X, T} ->
            PolyTy =
                case maps:find(X, Ctx#ctx.env) of
                    {ok, U} -> U;
                    error ->
                        case X of
                            {local_ref, Y} ->
                                errors:bug("Unbound variable in constraint simplification ~w", Y);
                            GlobalX ->
                                symtab:lookup_fun(GlobalX, loc(Locs), Ctx#ctx.symtab)
                        end
                end,
            {simp_constrs_ok, [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})]};
        {cop, Locs, OpName, OpArity, T} ->
            PolyTy = symtab:lookup_op(OpName, OpArity, loc(Locs), Ctx#ctx.symtab),
            {simp_constrs_ok, [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})]};
        {cdef, _Locs, Env, Cs} ->
            NewCtx = extend_env(Ctx, Env),
            simp_constrs(NewCtx, Cs);
        {ccase, Locs, CsScrut, {ExhauLeft, ExhauRight}, Bodies} ->
            case Ctx#ctx.sanity of
                {ok, TyMap0} ->
                    constr_gen:sanity_check(CsScrut, TyMap0);
                error -> ok
            end,
            simp_constrs_if_ok(
                simp_constrs(Ctx, CsScrut),
                fun(_, DssScrut) ->
                    FreeSet = tyutils:free_in_poly_env(Ctx#ctx.env),
                    ?LOG_DEBUG("Solving constraints for scrutiny of case at ~s in order to check " ++
                               "which branches should be ignored.~n" ++
                               "Env: ~s~nFixed tyvars: ~w~nConstraints for scrutiny:~n~s~n" ++
                               "exhaustivness check: ~s <= ~s",
                               ast:format_loc(loc(Locs)),
                               pretty:render_poly_env(Ctx#ctx.env),
                               sets:to_list(FreeSet),
                               pretty:render_constr(DssScrut),
                               pretty:render_ty(ExhauLeft),
                               pretty:render_ty(ExhauRight)),
                    Exhau = sets:from_list([{csubty, Locs, ExhauLeft, ExhauRight}]),
                    Substs =
                        lists:flatmap(
                          fun(DsScrut) ->
                                Ds = sets:union(DsScrut, Exhau),
                                get_substs(tally:tally(Ctx#ctx.symtab, Ds, FreeSet), Locs)
                          end,
                          DssScrut),
                    ?LOG_TRACE("Env=~s, FreeSet=~200p", pretty:render_poly_env(Ctx#ctx.env),
                            sets:to_list(FreeSet)),
                    case Substs of
                        [] -> ?LOG_DEBUG("No substitutions returned from tally."); % a type error is returned later
                        [{S, _}] -> ?LOG_DEBUG("Unique substitution:~n~s",
                                            pretty:render_subst(S));
                        L -> ?LOG_DEBUG("~w substitutions: ~s",
                                        length(L),
                                        pretty:render_substs(lists:map(fun({S, _}) -> S end, L)))
                    end,
                    % Non-determinism here because of multiple solutions from tally
                    % MultiResults has type [simp_constrs_result()]
                    % It contains a simp_constrs_result() for each substitution returned from tally.
                    MultiResults = lists:map(
                        fun({Subst, EquivDs}) ->
                                % returns simp_constrs_result(): if there is at least one
                                % branch that fails then the whole cases fails for the given
                                % substitution
                                lists:foldl(
                                    % returns simp_constrs_result()
                                    fun(_, {simp_constrs_error, _} = Err) -> Err;
                                       ({BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, TI}, BeforeDss) ->
                                            NewGuardsCtx = inter_env(Ctx, apply_subst_to_env(Subst, GuardsGammaI)),
                                            simp_constrs_if_ok(simp_constrs(NewGuardsCtx, GuardCsI),
                                                fun(GuardDss, _) ->
                                                    MatchTy = subst:apply(Subst, TI),
                                                    IsBottom = subty:is_subty(Ctx#ctx.symtab,
                                                                                MatchTy,
                                                                                {predef, none}),
                                                    case {IsBottom, Ctx#ctx.unmatched_branch} of
                                                        {true, ignore_branch} ->
                                                            ?LOG_DEBUG("Ignoring branch at ~s, match type ~s (unsubstituted: ~s) equivalent to none()",
                                                                        ast:format_loc(loc(BodyLocs)),
                                                                        pretty:render_ty(MatchTy),
                                                                        pretty:render_ty(TI)
                                                                        ),
                                                            cross_union(BeforeDss, GuardDss);
                                                        {true, report} ->
                                                            {simp_constrs_error, {redundant_branch, loc(BodyLocs)}};
                                                        _ ->
                                                            case Ctx#ctx.unmatched_branch of
                                                                ignore_branch ->
                                                                    ?LOG_DEBUG("Not ignoring branch at ~s, match type ~s (unsubstituted: ~s) greater than none()",
                                                                            ast:format_loc(loc(BodyLocs)),
                                                                            pretty:render_ty(MatchTy),
                                                                            pretty:render_ty(TI)
                                                                            );
                                                                _ -> ok
                                                            end,
                                                            NewBodyCtx =
                                                                inter_env(Ctx,
                                                                        apply_subst_to_env(Subst, BodyGammaI)),
                                                            BodyDss = simp_constrs(NewBodyCtx, BodyCsI),
                                                            cross_union(cross_union(BeforeDss, GuardDss), BodyDss)
                                                    end
                                                end)
                                    end,
                                    {simp_constrs_ok, [EquivDs]}, Bodies
                                )
                        end,
                        Substs
                    ),
                    ?LOG_TRACE("MultiResults: ~w", MultiResults),
                    case lists:filtermap(
                        fun({simp_constrs_ok, X}) -> {true, X};
                            (_) -> false
                        end,
                        MultiResults
                        )
                    of
                        % We have no successful results: either we only have errors or
                        % no results at all
                        [] ->
                            case lists:search(fun is_simp_constrs_error/1, MultiResults) of
                                false ->
                                    % MultiResults is empty, there is no substitution,
                                    % so the tally invocation for typing the scrutiny above failed.
                                    % Hence, we return an error
                                    ?LOG_DEBUG("MultiResults is empty, checking whether typing the scrutiny or the exhaustiveness check fails."),
                                    case
                                        lists:flatmap(
                                            fun(Ds) -> get_substs(tally:tally(Ctx#ctx.symtab, Ds, FreeSet), Locs) end,
                                        DssScrut)
                                    of
                                        [] ->
                                            ?LOG_DEBUG("Typing the scrutiny failed"),
                                            LocScrut = loc(locs_from_constrs(CsScrut), loc(Locs)),
                                            {simp_constrs_error, {tyerror, LocScrut}};
                                        _ ->
                                            ?LOG_DEBUG("Typing the scrutiny succeed, so it's a non-exhaustive case"),
                                            {simp_constrs_error, {non_exhaustive_case, loc(Locs)}}
                                    end;
                                {value, Err} ->
                                    % there are nested errors, return the first
                                    Err
                            end;
                        LL ->
                            % LL has type nonempty_list(nonempty_list(constr:simp_constrs())).
                            % It contains the successful results.
                            {simp_constrs_ok, lists:flatten(LL)}
                    end
                end);
        {cunsatisfiable, Locs, Msg} -> [single({cunsatisfiable, Locs, Msg})];
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

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
    subst:apply(Subst, T).

-spec single(T) -> sets:set(T).
single(X) -> sets:from_list([X]).

-spec loc(constr:locs()) -> ast:loc().
loc(Locs) ->
    case loc(Locs, error) of
        error -> errors:bug("empty set of locations");
        X -> X
    end.

-spec loc(constr:locs() | sets:set(ast:loc()), T) -> T | ast:loc().
loc({_, Locs}, Def) -> loc(Locs, Def);
loc(Locs, Def) ->
    case sets:to_list(Locs) of
        [First | Rest] ->
            lists:foldl(fun ast:min_loc/2, First, Rest);
        [] -> Def
    end.

-spec locs_from_constrs(constr:constrs()) -> sets:set(ast:loc()).
locs_from_constrs(Cs) ->
    sets:union(
        lists:map(
            fun (C) ->
                case C of
                    {csubty, {_, Locs}, _, _} -> Locs;
                    {cvar, {_, Locs}, _, _} -> Locs;
                    {cop, {_, Locs}, _, _, _} -> Locs;
                    {cdef, {_, Locs}, _, _} -> Locs;
                    {ccase, {_, Locs}, _, _, _} -> Locs;
                    {cunsatisfiable, L, _} -> sets:from_list([L])
                end
            end, sets:to_list(Cs))
    ).

-spec get_substs([subst:t()], constr:locs()) -> [{subst:t(), constr:simpl_constrs()}].
get_substs(Substs, Locs) ->
    case Substs of
        {error, _} ->
            % We cannot throw an error here because other branches might return a solvable constraint
            % set.
            [];
        L ->
            lists:map(
              fun(Subst) ->
                      Alphas = subst:domain(Subst),
                      EquivCs =
                          lists:foldl(
                            fun(Alpha, Acc) ->
                                    T = subst:apply(Subst, {var, Alpha}),
                                    sets:add_element(
                                      {csubty, Locs, T, {var, Alpha}},
                                      sets:add_element({csubty, Locs, {var, Alpha}, T}, Acc))
                            end,
                            sets:new(),
                            Alphas),
                      {Subst, EquivCs}
              end,
              L
             )
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

-spec apply_subst_to_env(subst:t(), constr:constr_env()) -> constr:constr_env().
apply_subst_to_env(Subst, Env) ->
    maps:map(fun(_Key, T) -> subst:apply(Subst, T) end, Env).

-spec sanity_check(any(), ast_check:ty_map()) -> ok.
sanity_check({simp_constrs_ok, Dss}, Spec) ->
    if
        not is_list(Dss) -> ?ABORT("List of constraint sets is not a list: ~w", Dss);
        true ->
            lists:foreach(
              fun(Ds) ->
                    case sets:is_set(Ds) of
                        false ->
                            ?ABORT("Expected set of simple constraints, got ~w", Ds);
                        true ->
                            lists:foreach(
                            fun(D) ->
                                    case ast_check:check_against_type(Spec, constr, simp_constr, D) of
                                        true ->
                                            ok;
                                        false ->
                                            ?ABORT("Invalid simple constraint generated: ~w", D)
                                    end
                            end,
                            sets:to_list(Ds))
                    end
              end,
              Dss)
    end;
sanity_check(_, _) -> ok.
