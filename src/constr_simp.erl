-module(constr_simp).

-include_lib("log.hrl").

-export([
    simp_constrs/2,
    new_ctx/5,
    sanity_check/2,
    simp_constrs_of_blocks/1
]).

-export_type([
    unmatched_branch_mode/0,
    simp_constrs_result/0,
    simp_constr_block/0
]).

-record(ctx,
        { symtab :: symtab:t(),
          env :: constr:constr_poly_env(),
          tyvar_counter :: counters:counters_ref(),
          sanity :: t:opt(ast_check:ty_map()),
          unmatched_branch :: unmatched_branch_mode(),
          fixed_tyvars :: sets:set(ast:ty_varname())
        }).
-type ctx() :: #ctx{}.

% unmatched_branch_mode specifies how we deal with branches of a case that cannot be
% matched. There are three possible alternatives:
%
% - unmatched_branch_ignore: specifies that branches of a case that cannot be matched
%   are excluded while type-checking.
% - unmatched_branch_report: report an error in case a branch cannot be match.
% - unmatched_branch_dont_check: do not check for unmatched branches at all.
%
% When type-checking a function against an intersection type, we use mode
% unmatched_branch_ignore.
%
% When type-checking a function against an non-intersection type, we use mode
% unmatched_branch_report.
%
% When inferring the type of a top-level function, we use mode unmatched_branch_dont_check.
%
% Currently, it is not possible to check for unmatched branches when type-checking
% against an intersection type. Here, we could report an error if the same branch
% is excluded for every element of the intersection. But this is not implemented.
-type unmatched_branch_mode() ::
    unmatched_branch_ignore | unmatched_branch_dont_check | unmatched_branch_report.

-spec new_ctx(symtab:t(),
             constr:constr_poly_env(),
             t:opt(ast_check:ty_map()),
             unmatched_branch_mode(),
             sets:set(ast:ty_varname())) -> ctx().
new_ctx(Tab, Env, Sanity, BranchMode, Fixed) ->
    Counter = counters:new(1, []),
    case BranchMode of
        unmatched_branch_ignore -> ok;
        unmatched_branch_dont_check -> ok;
        unmatched_branch_report -> ok;
        _ -> ?ABORT("Invalid value for unmatched_branch_mode: ~p", BranchMode)
    end,
    Ctx = #ctx{ tyvar_counter = Counter, env = Env, symtab = Tab, sanity = Sanity,
                unmatched_branch = BranchMode, fixed_tyvars = Fixed },
    Ctx.

% The result of constraint simplication is either a single error or a list of
% simp_constr_block() values. Each simp_constr_block() value carries a constraint set.
% A solution to the union of these constraint sets is a solution to the original constraint problem.
% The division into blocks enables better error reporting. Assume the C1,...,Cn are the constraint
% sets for all blocks. If the union of C1,...,Cn is not satisifiable, we first check whether
% C1 is not satisifiable. If not, then the first block gives the location of the error. Next,
% we check whether C1 \/ C2 is satisfiable. If not, then the second block gives the location of
% the error. And so on...
-type simp_constrs_result() ::
    {simp_constrs_ok, simp_constr_blocks()} |
    {simp_constrs_error, {simp_constrs_error_kind(), ast:loc()}}.

-type simp_constrs_error_kind() :: tyerror | redundant_branch | non_exhaustive_case.

-type simp_constr_blocks() :: [simp_constr_block()].

-type simp_constr_block() :: {simp_constr_block_kind(), ast:loc(), constr:simp_constrs()}.

-spec loc_of_block(simp_constr_block()) -> ast:loc().
loc_of_block({_, L, _}) -> L.

-type simp_constr_block_kind() :: simp_constr_block_exp | simp_constr_block_exhaustiveness.

-spec simp_constrs_of_blocks(simp_constr_blocks()) -> constr:simp_constrs().
simp_constrs_of_blocks(Blocks) ->
    sets:union(lists:map(fun ({_, _, Set}) -> Set end, Blocks)).

-spec simp_constrs(ctx(), constr:constrs()) -> simp_constrs_result().
simp_constrs(Ctx, Cs) ->
    try
        Res = simp_constrs_intern(Ctx, Cs),
        {simp_constrs_ok, Res}
    catch
        throw:{simp_constrs_error, X} ->
            {simp_constrs_error, X}
    end.

-spec simp_constrs_intern(ctx(), constr:constrs()) -> simp_constr_blocks().
simp_constrs_intern(Ctx, Cs) ->
    case sets:is_empty(Cs) of
        true -> [];
        false ->
            ?LOG_TRACE("simp_constrs, Cs=~s", pretty:render_constr(Cs)),
            % ListOfBlocks is a list of list of simp_constr_block().
            % The inner list has a meaningful ordering (namely by the structure of the program).
            % The outer list is randomly sorted (given by the order of sets:to_list(Cs)).
            ListOfBlocks = lists:map(
                fun(C) ->
                    ThisBlocks = simp_constr(Ctx, C),
                    case Ctx#ctx.sanity of
                        {ok, TyMap} ->
                            ThisDs = simp_constrs_of_blocks(ThisBlocks),
                            sanity_check(ThisDs, TyMap);
                        error -> ok
                    end,
                    ThisBlocks
                end,
                sets:to_list(Cs)),
            % We sort the outer list of blocks by the location of the first block
            SortedListOfBlocks =
                lists:sort(
                    fun (Blocks1, Blocks2) ->
                        case {Blocks1, Blocks2} of
                            {[], _} -> true;
                            {_, []} -> false;
                            {[B1 | _], [B2 | _]} ->
                                ast:leq_loc(loc_of_block(B1), loc_of_block(B2))
                        end
                    end,
                    ListOfBlocks),
            lists:concat(SortedListOfBlocks)
    end.

-spec simp_constr(ctx(), constr:constr()) -> simp_constr_blocks().
simp_constr(Ctx, C) ->
    ?LOG_TRACE("simp_constr, C=~w", C),
    case C of
        {csubty, Locs, _, _} -> [{simp_constr_block_exp, loc(Locs), single(C)}];
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
            [{simp_constr_block_exp, loc(Locs),
                single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})}];
        {cop, Locs, OpName, OpArity, T} ->
            PolyTy = symtab:lookup_op(OpName, OpArity, loc(Locs), Ctx#ctx.symtab),
            [{simp_constr_block_exp, loc(Locs),
                single({csubty, Locs, fresh_ty_scheme(Ctx, PolyTy), T})}];
        {cdef, _Locs, Env, Cs} ->
            NewCtx = extend_env(Ctx, Env),
            simp_constrs_intern(NewCtx, Cs);
        {ccase, Locs, CsScrut, Bodies} ->
            case Ctx#ctx.sanity of
                {ok, TyMap0} ->
                    constr_gen:sanity_check(CsScrut, TyMap0);
                error -> ok
            end,
            Ds = simp_constrs_of_blocks(simp_constrs_intern(Ctx, CsScrut)),
            CaseBlock = {simp_constr_block_exp, loc(Locs), Ds},
            % FIXME: extra block for exhaustiveness
            L = lists:flatmap(fun (Body) -> simp_case_body(Ctx, Body) end, Bodies),
            [CaseBlock | L];
        {cunsatisfiable, Locs, Msg} ->
            [{simp_constr_block_exp, loc(Locs), single({cunsatisfiable, Locs, Msg})}];
        X -> errors:uncovered_case(?FILE, ?LINE, X)
    end.

-spec single(T) -> sets:set(T).
single(X) -> sets:from_list([X]).

-spec simp_case_body(ctx(), constr:constr_case_body()) -> simp_constr_blocks().
simp_case_body(Ctx, {ccase_body, BodyLocs, {GuardsGammaI, GuardCsI}, {BodyGammaI, BodyCsI}, ReduCsOrNone}) ->
    FormattedLocs = ast:format_loc(loc(BodyLocs)),
    BranchIsRedundant =
        case {ReduCsOrNone, Ctx#ctx.unmatched_branch} of
            {none, _} -> false;
            {_, unmatched_branch_dont_check} -> false;
            {ReduCs, _} ->
                ReduDs = simp_constrs_of_blocks(simp_constrs_intern(Ctx, ReduCs)),
                case utils:timing_log(
                    fun () -> tally:tally(Ctx#ctx.symtab, ReduDs, Ctx#ctx.fixed_tyvars) end,
                    10,
                    utils:sformat("tally time for redundancy checking of branch ~s", FormattedLocs))
                of
                    {error, _} ->
                        % ReduDs is not satisfiable => Branch could match
                        false;
                    [Subst | _] ->
                        ?LOG_DEBUG(
                            "Branch at ~s can never match, redundancy constraints satisfiable ~s. First substitution: ~s",
                            FormattedLocs,
                            pretty:render_constr(ReduDs),
                            pretty:render_subst(Subst)
                            ),
                        true
                end
        end,
    NewGuardsCtx = inter_env(Ctx, GuardsGammaI),
    GuardsBlocks = simp_constrs_intern(NewGuardsCtx, GuardCsI),
    case {BranchIsRedundant, Ctx#ctx.unmatched_branch} of
        {true, unmatched_branch_ignore} ->
            ?LOG_DEBUG("Ignoring branch at ~s", FormattedLocs),
            GuardsBlocks;
        {true, unmatched_branch_report} ->
            ?LOG_DEBUG("Branch at ~s is redundant, reporting this as an error", FormattedLocs),
            throw({simp_constrs_error, {redundant_branch, loc(BodyLocs)}});
        _ ->
            case Ctx#ctx.unmatched_branch of
                unmatched_branch_ignore -> ?LOG_DEBUG("Not ignoring branch at ~s", FormattedLocs);
                _ -> ok
            end,
            NewBodyCtx = inter_env(Ctx, BodyGammaI),
            BodyBlocks = simp_constrs_intern(NewBodyCtx, BodyCsI),
            GuardsBlocks ++ BodyBlocks
    end.

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
    subst:apply(Subst, T).

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

-spec sanity_check(any(), ast_check:ty_map()) -> ok.
sanity_check(Ds, Spec) ->
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
    end.
