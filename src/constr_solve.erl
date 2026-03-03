-module(constr_solve).

-include("log.hrl").

-export([
    check_simp_constrs/5,
    check_simp_constrs_return_unmatched/5,
    solve_simp_constrs/4
]).

-export_type([
    error/0,
    error_kind/0
]).

-ifdef(TEST).
-export([search_failing_prefix/3]).
-endif.

-type error_kind() :: constr_error_locs:constr_error_kind().
-type error() :: {error_kind(), ast:loc(), string()}.

-include("etylizer.hrl").

% Ignores unmatched branches, just returns their locations.
-spec check_simp_constrs_return_unmatched(
    symtab:t(),
    sets:set(ast:ty_varname()),
    constr:simp_constrs(),
    string(),
    feature_flags:dump_tally_constraints()) ->
    {ok, Unmachted::sets:set(ast:loc())} | {error, error() | none}.
check_simp_constrs_return_unmatched(Tab, FixedTyvars, Ds, What, DumpMode) ->
    % ?LOG_DEBUG("Constraints:~n~s", pretty:render_constr(Ds)),
    SubtyConstrsDisj = constr_collect:collect_constrs_all_combinations(Ds),
    N = length(SubtyConstrsDisj),
    ?LOG_DEBUG("Found ~w conjunctions of constraints while type checking ~s", N, What),
    % SubtyConstrsDisj contains, for each conjunction, a set of
    % locations of branches that are switched off (do not match). If a conjunction
    % is satisifiable, we must return the set of locations. If a location is contained
    % in all sets for all intersection types, the branch at this location never matches,
    % so it's an error.
    case lists:foldl(
        fun ({I, {SwitchedOffBranches, RawConstrs}}, Acc) ->
            case Acc of
                false ->
                    dump_tally_constraints(raw, DumpMode, What, {conjunction, I, N}, RawConstrs),
                    ?LOG_DEBUG("Checking conjunction ~w/~w for satisfiability:~n~s",
                        I, N, pretty:render_constr(RawConstrs)),
                    case is_satisfiable(Tab, RawConstrs, FixedTyvars, "satisfiability check", DumpMode, What) of
                        false -> false;
                        true -> {true, SwitchedOffBranches}
                    end;
                {true, X} -> {true, X}
            end
        end,
        false,
        utils:with_index(1, SubtyConstrsDisj))
    of
        {true, SwitchedOffBranches} -> {ok, SwitchedOffBranches};
        false -> {error, none} % FIXME: error locations
    end.

% Check if dynamic() appears anywhere in the constraint set.
% If so, redundancy checks are skipped entirely because dynamic() is consistent
% with both T and not(T) for any T, making the satisfiability-based redundancy
% check unsound.
-spec has_dynamic_constr(symtab:t(), constr:collected_constrs()) -> boolean().
has_dynamic_constr(Tab, Constrs) ->
    TyHasDynamic = fun(Ty) ->
        Unfolded = ast_utils:unfold_ty(Tab, Ty),
        utils:everything(
            fun ({predef, dynamic}) -> {ok, true};
                (_) -> error
            end, Unfolded) =/= []
    end,
    lists:any(
        fun ({scsubty, _, T1, T2}) -> TyHasDynamic(T1) orelse TyHasDynamic(T2);
            ({scmater, _, T1, _}) -> TyHasDynamic(T1);
            (_) -> false
        end,
        sets:to_list(Constrs)).

-spec check_redundant_branch(symtab:t(), sets:set(ast:ty_varname()), constr:collected_constrs(),
    {ast:loc(), constr:collected_constrs()}, ok | {error, error()}) -> ok | {error, error()}.
check_redundant_branch(_Tab, _FixedTyvars, _SubtyConstrs, _LocAndConstrs, Acc = {error, _}) -> Acc;
check_redundant_branch(Tab, FixedTyvars, SubtyConstrs, {Loc, UnmatchedConstrs}, ok) ->
    All = sets:union(UnmatchedConstrs, SubtyConstrs),
    case is_satisfiable(Tab, All, FixedTyvars, "redundancy check") of
        true ->
            ?LOG_DEBUG("Branch at ~s is redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                ast:format_loc(Loc),
                pretty:render_list(fun pretty:constr_simp/1, sets:to_list(UnmatchedConstrs)),
                sets:to_list(FixedTyvars)),
            {error, {redundant_branch, Loc, ""}};
        false ->
            ?LOG_DEBUG("Branch at ~s is not redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                ast:format_loc(Loc),
                pretty:render_list(fun pretty:constr_simp/1, sets:to_list(UnmatchedConstrs)),
                sets:to_list(FixedTyvars)),
            ok
    end.

-spec check_redundant_branch_incr(symtab:t(), sets:set(ast:ty_varname()),
    tally:base_sat_result(),
    {ast:loc(), constr:collected_constrs()}, ok | {error, error()}) -> ok | {error, error()}.
check_redundant_branch_incr(_Tab, _FixedTyvars, _BaseResult, _LocAndConstrs, Acc = {error, _}) -> Acc;
check_redundant_branch_incr(Tab, FixedTyvars, BaseResult, {Loc, UnmatchedConstrs}, ok) ->
    {Satisfiable, Delta} = utils:timing(fun() ->
        tally:is_satisfiable_incremental(Tab, BaseResult, UnmatchedConstrs, FixedTyvars)
    end),
    case Satisfiable of
        true ->
            ?LOG_DEBUG("Tally time (redundancy check incr): ~pms, tally successful.", Delta),
            ?LOG_DEBUG("Branch at ~s is redundant.",
                ast:format_loc(Loc)),
            {error, {redundant_branch, Loc, ""}};
        false ->
            ?LOG_DEBUG("Tally time (redundancy check incr): ~pms, tally finished with errors.", Delta),
            ?LOG_DEBUG("Branch at ~s is not redundant.",
                ast:format_loc(Loc)),
            ok
    end.

-spec locate_unsat_error(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs()) ->
    {error, error() | none}.
locate_unsat_error(Tab, FixedTyvars, Ds) ->
    Blocks = constr_error_locs:simp_constrs_to_blocks(Ds),
    ?LOG_DEBUG("Constraints are not satisfiable, now locating source of errors. ~w blocks",
        length(Blocks)),
    Timeout = 4000,
    TimeoutRes = utils:timeout(Timeout, fun () -> locate_tyerror(Tab, FixedTyvars, Blocks) end),
    case TimeoutRes of
        {ok, Res} -> Res;
        timeout ->
            ?LOG_INFO("Locating type error timed out after ~wms", Timeout),
            {error, none}
    end.

% Treats unmatched branches as errors.
-spec check_simp_constrs(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs(), string(),
    feature_flags:dump_tally_constraints()) ->
    ok | {error, error() | none}.
check_simp_constrs(Tab, FixedTyvars, Ds, What, DumpMode) ->
    RawConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    dump_tally_constraints(raw, DumpMode, What, single, RawConstrs),
    {SubtyConstrs, _MaterSubst} = gradual_utils:inline_materializations(RawConstrs),
    ?LOG_DEBUG("Checking constraints for satisfiability to type check ~s:~n~s~nFixed: ~s",
        What, pretty:render_list(fun pretty:constr_simp/1, sets:to_list(SubtyConstrs)), pretty:render_set(fun pretty:atom/1, FixedTyvars)),
    case check_nominal_constrs(Tab, SubtyConstrs) of
        {error, NomErr} -> {error, NomErr};
        ok ->
            case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check", DumpMode, What) of
                true ->
                    ReduDs = constr_collect:collect_matching_cond_constrs(Ds),
                    case ReduDs of
                        [] -> ok;
                        _ ->
                            ?LOG_DEBUG("Constraints are satisfiable, now checking ~w branches for redundancy (incremental)",
                                length(ReduDs)),
                            % Compute base solutions (without AST optimizations) for incremental merging.
                            case tally:is_satisfiable_base(Tab, RawConstrs, FixedTyvars) of
                                {true, BaseResult} ->
                                    case has_dynamic_constr(Tab, SubtyConstrs) of
                                        true ->
                                            ?LOG_DEBUG("Skipping all redundancy checks (dynamic() found in constraints)"),
                                            ok;
                                        false ->
                                            lists:foldl(
                                                fun (LocAndConstrs, Acc) ->
                                                    check_redundant_branch_incr(Tab, FixedTyvars, BaseResult, LocAndConstrs, Acc)
                                                end,
                                                ok,
                                                ReduDs)
                                    end;
                                {false, _} ->
                                    % Main check passed but base failed — shouldn't happen, treat as ok.
                                    ok
                            end
                    end;
                false ->
                    locate_unsat_error(Tab, FixedTyvars, Ds)
            end
    end.

% search_failing_prefix(L, F, Pred, Acc).
% Returns the list element Xi of L with the smallest index i such that
% Pred(F(X1) union ... union F(Xi)) yields false.
% That is, for all j < i: Pred(Acc union F(X1) union ... union F(Xj)) yields true.
% Precondition: Pred(F(X1) union ... union F(Xn)), where n is the length of L, must be false.
-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean())) -> T.
search_failing_prefix([], _, _) -> erlang:error({search_failing_prefix, empty_list});
search_failing_prefix([_ | _] = L, F, Pred) ->
    N = length(L),
    ?LOG_DEBUG("Search for a minimal unsatisfiable prefix in ~w blocks", N),
    I = search_failing_prefix(L, F, Pred, 1, N),
    lists:nth(I, L).

% Helper function for search_failing_prefix.
% We some sort of binary search here to minimize the calls of Pred. (In reality, Pred is tally,
% which is expensive.)
% Left and Right are the (inclusive) boundaries of the search, starting at 1.
% Invariants: Left <= Right and Pred(F(X1) union ... union F(X_Right)) yields false
-spec search_failing_prefix(
    nonempty_list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean()), pos_integer(), pos_integer())
    -> pos_integer().
search_failing_prefix([_ | _] = L, F, Pred, Left, Right) ->
    Mid = max(1, (Left + Right) div 2),
    Prefix = lists:sublist(L, Mid), % take all elements until Mid (inclusive)
    ?LOG_DEBUG("Checking if the first ~w blocks are satisifiable", Mid),
    Set = sets:union([F(X) || X <- Prefix]),
    Res = Pred(Set),
    % io:format("  Left=~w, Right=~w, Mid=~w, Res=~w, Prefix=~w~n", [Left, Right, Mid, Res, Prefix]),
    case Res of
        false ->
            case Left >= Right of
                true -> Mid;
                false -> search_failing_prefix(L, F, Pred, Left, Mid)
            end;
        true ->
            case Left >= Right of
                true -> Right;
                false -> search_failing_prefix(L, F, Pred, Mid + 1, Right)
            end
    end.

-spec locate_tyerror(symtab:t(), sets:set(ast:ty_varname()), constr_error_locs:constr_blocks())
    -> {error, error() | none}.
locate_tyerror(Tab, FreeSet, Blocks) ->
    Extract = fun({_Kind, _Span, _What, Ds}) -> Ds end,
    Pred = fun(Ds) -> is_satisfiable(Tab, Ds, FreeSet, "error location", none, "") end,
    {Kind, Span, _What, _Ds} = search_failing_prefix(Blocks, Extract, Pred),
    {error, {Kind, Span, ""}}.

-spec format_tally_error([{error, string()}]) -> string().
format_tally_error([]) -> "(no specific error messages)";
format_tally_error(ErrList) ->
    {ErrListShort, N} = utils:shorten(ErrList, 20),
    "\n" ++ string:join(
      lists:map(
        fun({error, Msg}) -> "    " ++ Msg end, ErrListShort),
      "\n") ++
    (if N =:= 0 -> "";
        true -> utils:sformat("~n    (skipped ~w lines)", N)
     end).

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname()), string(),
    feature_flags:dump_tally_constraints(), string()) -> boolean().
is_satisfiable(Tab, Constrs, Fixed, What, DumpMode, FunName) ->
    {SatisfyRes, Delta} = utils:timing(fun() -> tally:is_satisfiable(Tab, Constrs, Fixed, DumpMode, FunName) end),
    case SatisfyRes of
        {false, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            false;
        {true, _} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            true
    end.

% Checks for nominal type incompatibilities in the collected constraints.
% Two nominal types with different names are never compatible.
% A nominal type is compatible with a non-nominal structural type (both directions).
-spec check_nominal_constrs(symtab:t(), constr:collected_constrs()) -> ok | {error, error()}.
check_nominal_constrs(Tab, Constrs) ->
    ConstrList = sets:to_list(Constrs),
    MaterMap = build_mater_map(ConstrList),
    lists:foldl(
        fun
            (_, {error, _} = Err) -> Err;
            ({scsubty, Loc, T1, T2}, ok) ->
                RT1 = resolve_vars(T1, MaterMap),
                RT2 = resolve_vars(T2, MaterMap),
                check_nominal_pair(Tab, Loc, RT1, RT2);
            (_, ok) -> ok
        end,
        ok,
        ConstrList).

-spec build_mater_map([constr:simp_constr_subty() | constr:simp_constr_mater()]) ->
    #{ast:ty_varname() => ast:ty()}.
build_mater_map(Constrs) ->
    lists:foldl(
        fun(C, Acc) ->
            case C of
                {scmater, _, T, Alpha} -> maps:put(Alpha, T, Acc);
                _ -> Acc
            end
        end,
        #{},
        Constrs).

% Resolve type variables through the materialization map (one level).
-spec resolve_vars(ast:ty(), #{ast:ty_varname() => ast:ty()}) -> ast:ty().
resolve_vars({var, Alpha}, MaterMap) ->
    case maps:find(Alpha, MaterMap) of
        {ok, T} -> T;
        error -> {var, Alpha}
    end;
resolve_vars(T, _) -> T.

% Check a pair of types for nominal incompatibility.
% Only checks top-level named types and recurses into compound types.
-spec check_nominal_pair(symtab:t(), ast:loc(), ast:ty(), ast:ty()) -> ok | {error, error()}.
check_nominal_pair(Tab, Loc, T1, T2) ->
    case {T1, T2} of
        {{named, _, Ref1, _}, {named, _, Ref2, _}} ->
            case {symtab:is_nominal(Ref1, Tab), symtab:is_nominal(Ref2, Tab)} of
                {true, true} ->
                    case refs_equal(Ref1, Ref2) of
                        true -> ok;
                        false -> {error, {nominal_incompatible, Loc, ""}}
                    end;
                _ -> ok
            end;
        {{tuple, Elems1}, {tuple, Elems2}} when length(Elems1) =:= length(Elems2) ->
            check_nominal_pairs(Tab, Loc, Elems1, Elems2);
        {{list, E1}, {list, E2}} ->
            check_nominal_pair(Tab, Loc, E1, E2);
        {{nonempty_list, E1}, {nonempty_list, E2}} ->
            check_nominal_pair(Tab, Loc, E1, E2);
        {{fun_full, Args1, Ret1}, {fun_full, Args2, Ret2}} when length(Args1) =:= length(Args2) ->
            case check_nominal_pairs(Tab, Loc, Args1, Args2) of
                ok -> check_nominal_pair(Tab, Loc, Ret1, Ret2);
                Err -> Err
            end;
        _ -> ok
    end.

-spec check_nominal_pairs(symtab:t(), ast:loc(), [ast:ty()], [ast:ty()]) -> ok | {error, error()}.
check_nominal_pairs(_Tab, _Loc, [], []) -> ok;
check_nominal_pairs(Tab, Loc, [T1 | Rest1], [T2 | Rest2]) ->
    case check_nominal_pair(Tab, Loc, T1, T2) of
        ok -> check_nominal_pairs(Tab, Loc, Rest1, Rest2);
        Err -> Err
    end;
check_nominal_pairs(_Tab, _Loc, _, _) -> ok.

-spec refs_equal(ast:ty_ref(), ast:ty_ref()) -> boolean().
refs_equal(Ref1, Ref2) ->
    normalize_ref(Ref1) =:= normalize_ref(Ref2).

-spec normalize_ref(ast:ty_ref()) -> {atom(), atom(), arity()}.
normalize_ref({ty_ref, M, N, A}) -> {M, N, A};
normalize_ref({ty_qref, M, N, A}) -> {M, N, A}.

-spec solve_simp_constrs(symtab:t(), constr:simp_constrs(), string(), feature_flags:dump_tally_constraints()) -> error | nonempty_list(subst:t()).
solve_simp_constrs(Tab, Ds, What, DumpMode) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    dump_tally_constraints(raw, DumpMode, What, single, SubtyConstrs),
    {Res, Delta} = utils:timing(fun() -> tally:tally(Tab, SubtyConstrs, DumpMode, What) end),
    case Res of
        {error, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            error;
        Substs ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            ?LOG_TRACE("Substitutions:~n~s", [pretty:render_substs(Substs)]),
            Substs
    end.

% Dump collected constraints to stdout when the dump mode matches.
-spec dump_tally_constraints(raw | simplified, feature_flags:dump_tally_constraints(), string(),
    single | {conjunction, pos_integer(), pos_integer()}, constr:collected_constrs()) -> ok.
dump_tally_constraints(Phase, DumpMode, What, Scope, Constrs) ->
    case Phase =:= DumpMode of
        false -> ok;
        true ->
            Header = case Scope of
                single -> utils:sformat("[~s] ~s constraints for ~s", Phase, atom_to_list(Phase), What);
                {conjunction, I, N} -> utils:sformat("[~s] ~s constraints for ~s (conjunction ~w/~w)", Phase, atom_to_list(Phase), What, I, N)
            end,
            Rendered = pretty:render_list(fun pretty:constr_simp/1, sets:to_list(Constrs)),
            io:format(user, "~s:~n~s~n", [Header, Rendered])
    end.
