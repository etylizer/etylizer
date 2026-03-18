-module(constr_solve).

-include("log.hrl").

-export([
    check_simp_constrs/4,
    check_simp_constrs_return_unmatched/4,
    solve_simp_constrs/3
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

% Ignores unmatched branches, just returns their locations.
-spec check_simp_constrs_return_unmatched(
    symtab:t(),
    sets:set(ast:ty_varname()),
    constr:simp_constrs(),
    string()) ->
    {ok, Unmachted::sets:set(ast:loc())} | {error, error() | none}.
check_simp_constrs_return_unmatched(Tab, FixedTyvars, Ds, What) ->
    SubtyConstrsDisj = constr_collect:collect_constrs_all_combinations(Ds),
    N = length(SubtyConstrsDisj),
    ?LOG_DEBUG("Found ~w conjunctions of constraints while type checking ~s", N, What),
    case lists:foldl(
        fun ({I, {SwitchedOffBranches, SubtyConstrs}}, Acc) ->
            case Acc of
                false ->
                    ?LOG_DEBUG("Checking conjunction ~w/~w for satisfiability:~n~s",
                        I, N, pretty:render_constr(SubtyConstrs)),
                    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
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
        false -> {error, none}
    end.

% Check if dynamic() appears anywhere in the constraint set.
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

% Nominal types present and structural check passed: check nominal compatibility.
-spec check_nominal_after_structural(symtab:t(), constr:simp_constrs(), constr:collected_constrs()) ->
    ok | {error, error()}.
check_nominal_after_structural(Tab, Ds, SubtyConstrs) ->
    case constr_solve_nominal:check_nominal_constrs(Tab, SubtyConstrs) of
        ok -> ok;
        {error, _} ->
            SubtyConstrsDisj = constr_collect:collect_constrs_all_combinations(Ds),
            ?LOG_DEBUG("Nominal conflict on flattened set, checking ~w combinations", length(SubtyConstrsDisj)),
            constr_solve_nominal:check_nominal_combinations_only(Tab, SubtyConstrsDisj)
    end.

% Check for redundant branches using incremental satisfiability.
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
            ?LOG_DEBUG("Branch at ~s is redundant.", ast:format_loc(Loc)),
            {error, {redundant_branch, Loc, ""}};
        false ->
            ?LOG_DEBUG("Tally time (redundancy check incr): ~pms, tally finished with errors.", Delta),
            ?LOG_DEBUG("Branch at ~s is not redundant.", ast:format_loc(Loc)),
            ok
    end.

-spec locate_unsat_error(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs()) ->
    {error, error() | none}.
locate_unsat_error(Tab, FixedTyvars, Ds) ->
    Blocks = constr_error_locs:simp_constrs_to_blocks(Ds),
    ?LOG_DEBUG("Constraints are not satisfiable, now locating source of errors. Blocks:~n~s",
        pretty:render_list(fun pretty:constr_block/1, Blocks)),
    Timeout = 4000,
    TimeoutRes = utils:timeout(Timeout, fun () -> locate_tyerror(Tab, FixedTyvars, Blocks) end),
    case TimeoutRes of
        {ok, Res} -> Res;
        timeout ->
            ?LOG_INFO("Locating type error timed out after ~wms", Timeout),
            {error, none}
    end.

% Treats unmatched branches as errors.
-spec check_simp_constrs(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs(), string()) ->
    ok | {error, error() | none}.
check_simp_constrs(Tab, FixedTyvars, Ds, What) ->
    RawConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    {SubtyConstrs, _MaterSubst} = gradual_utils:inline_materializations(RawConstrs),
    ?LOG_DEBUG("Checking constraints for satisfiability to type check ~s:~n~s~nFixed: ~s",
        What, pretty:render_list(fun pretty:constr_simp/1, sets:to_list(SubtyConstrs)), pretty:render_set(fun pretty:atom/1, FixedTyvars)),
    % Run structural check once on the flattened constraint set
    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
        true ->
            % Structurally satisfiable; now check for nominal conflicts if needed
            NomResult = case symtab:has_any_nominals(Tab) andalso constr_solve_nominal:has_nominal_constrs(Tab, SubtyConstrs) of
                true ->
                    check_nominal_after_structural(Tab, Ds, SubtyConstrs);
                false ->
                    ok
            end,
            case NomResult of
                ok ->
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
                                    % Main check passed but base failed -- treat as ok.
                                    ok
                            end
                    end;
                {error, _} = Err -> Err
            end;
        false ->
            locate_unsat_error(Tab, FixedTyvars, Ds)
    end.

% search_failing_prefix(L, F, Pred, Acc).
-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean())) -> T.
search_failing_prefix(L, F, Pred) ->
    N = length(L),
    ?LOG_DEBUG("Search for a minimal unsatisfiable prefix in ~w blocks", N),
    I = search_failing_prefix(L, F, Pred, 1, N),
    lists:nth(I, L).

-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean()), integer(), integer())
    -> integer().
search_failing_prefix(L, F, Pred, Left, Right) ->
    Mid = (Left + Right) div 2,
    Prefix = lists:sublist(L, Mid),
    ?LOG_DEBUG("Checking if the first ~w blocks are satisifiable", Mid),
    Set = sets:union(lists:map(F, Prefix)),
    Res = Pred(Set),
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
    Pred = fun(Ds) -> is_satisfiable(Tab, Ds, FreeSet, "error location") end,
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

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname()), string()) -> boolean().
is_satisfiable(Tab, Constrs, Fixed, What) ->
    {SatisfyRes, Delta} = utils:timing(fun() -> tally:is_satisfiable(Tab, Constrs, Fixed) end),
    case SatisfyRes of
        {false, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            false;
        {true, _} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            true
    end.

-spec solve_simp_constrs(symtab:t(), constr:simp_constrs(), string()) -> error | nonempty_list(subst:t()).
solve_simp_constrs(Tab, Ds, What) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    {Res, Delta} = utils:timing(fun() -> tally:tally(Tab, SubtyConstrs) end),
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
