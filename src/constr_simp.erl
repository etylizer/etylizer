-module(constr_simp).

-include_lib("log.hrl").

-export([
    simp_constrs/2,
    new_ctx/4,
    sanity_check/3
]).

-export_type([unmatched_branch_mode/0]).

-record(ctx,
        { symtab :: symtab:t(),
          env :: constr:constr_poly_env(),
          tyvar_counter :: counters:counters_ref(),
          sanity :: t:opt(ast_spec:ty_map()),
          unmatched_branch :: unmatched_branch_mode()
        }).
-type ctx() :: #ctx{}.

% Mode ignore_branch specifies that branches of a case that cannot be matched
% are excluded while type-checking. This mode leads to non-determinism as we need
% tally in order to detect whether a branch can match or not.
%
% Mode report should report an error in case a branch cannot be match.
% To avoid invoking tally, this mode does not actually report an error but
% returns a matching type. The idea is that we later check if the matching type
% turns out to be a subtype of none(), and if yes, then report the error.
% But this is not implemented.
%
% When type-checking a function against an intersection type, we use mode
% ignore_branch. Otherwise, we use report.
%
% Currently, it is not possible to check for unmatched branches when type-checking
% against an intersection type. Here, we could report an error if the same branch
% is excluded for every element of the intersection.
-type unmatched_branch_mode() :: ignore_branch | report.

-spec new_ctx(symtab:t(), constr:constr_poly_env(),
              t:opt(ast_spec:ty_map()), unmatched_branch_mode()) -> ctx().
new_ctx(Tab, Env, Sanity, BranchMode) ->
    Counter = counters:new(1, []),
    Ctx = #ctx{ tyvar_counter = Counter, env = Env, symtab = Tab, sanity = Sanity,
                unmatched_branch = BranchMode },
    Ctx.

-spec simp_constrs(ctx(), constr:constrs()) -> [constr:simp_constrs()].
simp_constrs(Ctx, Cs) ->
    ?LOG_TRACE("simp_constrs, Cs=~w", Cs),
    sets:fold(
      fun(C, Dss2) ->
              % returns [constr:simp_constrs()]
              Dss1 = simp_constr(Ctx, C),
              case Ctx#ctx.sanity of
                  {ok, TyMap} -> sanity_check(Dss1, TyMap, Ctx#ctx.unmatched_branch);
                  error -> ok
              end,
              cross_union(Dss1, Dss2)
      end,
      [sets:new()], Cs).

-spec simp_constr(ctx(), constr:constr()) -> [constr:simp_constrs()].
simp_constr(Ctx, C) ->
    ?LOG_TRACE("simp_constr, C=~w", C),
    case C of
        {csubty, _, _, _} -> [single(C)];
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
            [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})];
        {cop, Locs, OpName, OpArity, T} ->
            PolyTy = symtab:lookup_op(OpName, OpArity, loc(Locs), Ctx#ctx.symtab),
            [single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})];
        {cdef, _Locs, Env, Cs} ->
            NewCtx = extend_env(Ctx, Env),
            simp_constrs(NewCtx, Cs);
        {ccase, Locs, Cs, Bodies} ->
            case Ctx#ctx.sanity of
                {ok, TyMap0} -> constr_gen:sanity_check(Cs, TyMap0);
                error -> ok
            end,
            Dss = simp_constrs(Ctx, Cs),
            case Ctx#ctx.unmatched_branch of
                ignore_branch ->
                    % NOTE: there is some code duplication with respect to the report case
                    FreeSet = tyutils:free_in_poly_env(Ctx#ctx.env),
                    Substs =
                        lists:flatmap(
                          fun(Ds) ->
                                  ?LOG_DEBUG("Invoking tally while simplifying constraints. " ++
                                                 "FreeSet=~w, Constraints:~n~s",
                                             sets:to_list(FreeSet),
                                             pretty:render_constr(Ds)),
                                  get_substs(tally:tally(Ctx#ctx.symtab, Ds, FreeSet), Locs)
                          end,
                          Dss),
                    ?LOG_DEBUG("Checking which branches of case at ~s should be ignored.~n" ++
                               "Fixed tyvars: ~w~nConstraints:~n~s",
                               ast:format_loc(loc(Locs)),
                               sets:to_list(FreeSet),
                               pretty:render_constr(Dss)),
                    ?LOG_TRACE("Env=~s, FreeSet=~200p", pretty:render_poly_env(Ctx#ctx.env),
                               sets:to_list(FreeSet)),
                    case Substs of
                        [] -> ?LOG_DEBUG("No substitutions returned from tally.");
                        [{S, _}] -> ?LOG_DEBUG("Unique substitution:~n~s",
                                               pretty:render_subst(S));
                        L -> ?LOG_DEBUG("~w substitutions: ~s",
                                        length(L),
                                        pretty:render_substs(lists:map(fun({S, _}) -> S end, L)))
                    end,
                    % Non-determinism here because of multiple solutions from tally
                    lists:flatmap(
                      fun({Subst, EquivDs}) ->
                              % returns [constr:simp_constrs()]
                              lists:foldl(
                                % returns [constr:simp_constrs()]
                                fun({BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, TI}, BeforeDss) ->
                                        NewGuardsCtx =
                                            extend_env(Ctx,
                                                       apply_subst_to_env(Subst, GuardsGammaI)),
                                        GuardDss = simp_constrs(NewGuardsCtx, GuardCsI),
                                        MatchTy = subst:apply(Subst, TI),
                                        IsBottom = subty:is_subty(Ctx#ctx.symtab,
                                                                  MatchTy,
                                                                  {predef, none}),
                                        if IsBottom ->
                                                ?LOG_DEBUG("Ignoring branch at ~s, match type ~s (unsubstituted: ~s) equivalent to none()",
                                                           ast:format_loc(loc(BodyLocs)),
                                                           pretty:render_ty(MatchTy),
                                                           pretty:render_ty(TI)
                                                          ),
                                                cross_union(BeforeDss, GuardDss);
                                           true ->
                                                ?LOG_DEBUG("Not ignoring branch at ~s, match type ~s (unsubstituted: gb~s) greater than none()",
                                                           ast:format_loc(loc(BodyLocs)),
                                                           pretty:render_ty(MatchTy),
                                                           pretty:render_ty(TI)
                                                          ),
                                                NewBodyCtx =
                                                    extend_env(Ctx,
                                                               apply_subst_to_env(Subst, BodyGammaI)),
                                                BodyDss = simp_constrs(NewBodyCtx, BodyCsI),
                                                cross_union(cross_union(BeforeDss, GuardDss), BodyDss)
                                        end
                                end,
                                [EquivDs], Bodies
                               )
                      end,
                      Substs
                     );
                report ->
                    % NOTE: there is some code duplication with respect to the ignore_branch case
                    lists:foldl(
                      fun({_BodyLoc, {GuardsGammaI, GuardCsI}, {BodyGammI, BodyCsI}, _TI}, BeforeDss) ->
                              % returns [constr:simp_constrs()]
                              % FIXME: we need to return the matching type TI
                              GuardDss = simp_constrs(extend_env(Ctx, GuardsGammaI), GuardCsI),
                              BodyDss = simp_constrs(extend_env(Ctx, BodyGammI), BodyCsI),
                              cross_union(cross_union(BeforeDss, GuardDss), BodyDss)
                      end,
                      Dss, Bodies
                     )
            end;
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
loc({_, Locs}) ->
    case sets:to_list(Locs) of
        [L | _] -> L;
        [] -> errors:bug("empty set of locations")
    end.

-spec get_substs([subst:t()], constr:locs()) -> [{subst:t(), constr:simpl_constrs()}].
get_substs(Substs, Locs) ->
    case Substs of
        {error, _} ->
            % We cannot throw an error here because other branches might return a solvable constraint
            % set. TODO: give a meaningful error message if no constraint set at all can be returned.
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
    Ctx#ctx { env = NewEnv }.

-spec apply_subst_to_env(subst:t(), constr:constr_env()) -> constr:constr_env().
apply_subst_to_env(Subst, Env) ->
    maps:map(fun(_Key, T) -> subst:apply(Subst, T) end, Env).

-spec cross_union([sets:set(T)], [sets:set(T)]) -> [sets:set(T)].
cross_union(L1, L2) ->
    lists:flatmap(
      fun(S1) ->
              lists:map(fun(S2) -> sets:union(S1, S2) end, L2)
      end,
      L1).

-spec sanity_check([constr:simp_constrs()], ast_spec:ty_map(), unmatched_branch_mode()) -> ok.
sanity_check(Dss, Spec, BranchMode) ->
    case is_list(Dss) of
        false -> ?ABORT("List of constraint sets is not a list: ~w", Dss);
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
              Dss),
           case {BranchMode, Dss} of
               {report, [_]} -> ok;
               {report,  _} ->
                   ?ABORT("In branch mode 'report', no non-determinism should occur");
               _ -> ok
           end
    end.
