-module(constr_solve).

-include_lib("log.hrl").

-export([
    check_simp_constrs/4,
    check_simp_constrs_return_unmatched/4,
    solve_simp_constrs/3,
    search_failing_prefix/3
]).

-export_type([
    error/0,
    error_kind/0
]).

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
        false -> {error, none} % FIXME: error locations
    end.

% Treats unmatched branches as errors.
-spec check_simp_constrs(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs(), string()) ->
    ok | {error, error() | none}.
check_simp_constrs(Tab, FixedTyvars, Ds, What) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    ?LOG_DEBUG("Checking constraints for satisfiability to type check ~s:~n~s~nFixed: ~s",
        What, pretty:render_constr(SubtyConstrs), pretty:render_set(fun pretty:atom/1, FixedTyvars)),
    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
        true ->
            % check for redundant branches
            ReduDs = constr_collect:collect_matching_cond_constrs(Ds),
            ?LOG_DEBUG("Constraints are satisfiable, now checking ~w branches for redundancy",
                length(ReduDs)),
            lists:foldl(
                fun ({Loc, UnmatchedConstrs}, Acc) ->
                    case Acc of
                        ok ->
                            All = sets:union(UnmatchedConstrs, SubtyConstrs),
                            case is_satisfiable(Tab, All, FixedTyvars, "redundancy check") of
                                true ->
                                    ?LOG_DEBUG("Branch at ~s is redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                                        ast:format_loc(Loc),
                                        pretty:render_constr(UnmatchedConstrs),
                                        sets:to_list(FixedTyvars)),
                                    {error, {redundant_branch, Loc, ""}};
                                false ->
                                    ?LOG_DEBUG("Branch at ~s is not redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                                        ast:format_loc(Loc),
                                        pretty:render_constr(UnmatchedConstrs),
                                        sets:to_list(FixedTyvars)),
                                    ok
                            end;
                        _ -> Acc
                    end
                end,
                ok,
                ReduDs);
        false ->
            Blocks = constr_error_locs:simp_constrs_to_blocks(Ds),
            ?LOG_DEBUG("Constraints are not satisfiable, now locating source of errors. Blocks:~n~s",
                pretty:render_list(fun pretty:constr_block/1, Blocks)),
            Timeout = 2000,
            case utils:timeout(Timeout, fun () -> locate_tyerror(Tab, FixedTyvars, Blocks) end) of
                {ok, Res} -> Res;
                timeout ->
                    ?LOG_INFO("Locating type error timed out after ~wms", Timeout),
                    {error, none}
            end
    end.

% search_failing_prefix(L, F, Pred, Acc).
% Returns the list element Xi of L with the smallest index i such that
% Pred(F(X1) union ... union F(Xi)) yields false.
% That is, for all j < i: Pred(Acc union F(X1) union ... union F(Xj)) yields true.
% Precondition: Pred(F(X1) union ... union F(Xn)), where n is the length of L, must be false.
-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean())) -> T.
search_failing_prefix(L, F, Pred) ->
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
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean()), integer(), integer())
    -> integer().
search_failing_prefix(L, F, Pred, Left, Right) ->
    Mid = (Left + Right) div 2,
    Prefix = lists:sublist(L, Mid), % take all elements until Mid (inclusive)
    ?LOG_DEBUG("Checking if the first ~w blocks are satisifiable", Mid),
    Set = sets:union(lists:map(F, Prefix)),
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
    -> ok | {error, error() | none}.
locate_tyerror(Tab, FreeSet, Blocks) ->
    Extract = fun({_Kind, _Span, _What, Ds}) -> Ds end,
    Pred = fun(Ds) -> is_satisfiable(Tab, Ds, FreeSet, "error location") end,
    {Kind, Span, _What, _Ds} = search_failing_prefix(Blocks, Extract, Pred),
    {error, {Kind, Span, ""}}.

-spec format_tally_error([string()]) -> string().
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

-spec is_satisfiable(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname()), string()) -> boolean().
is_satisfiable(Tab, Constrs, Fixed, What) ->
    {SatisfyRes, Delta} = utils:timing(fun() -> tally:is_satisfiable(Tab, Constrs, Fixed) end),
    case SatisfyRes of
        {false, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            false;
        {true, S} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            ?LOG_TRACE("First substitution:~n~s", [pretty:render_subst(S)]),
            true
    end.

-spec solve_simp_constrs(symtab:t(), constr:subty_constrs(), string()) -> error | nonempty_list(subst:t()).
solve_simp_constrs(Tab, Ds, What) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    {Res, Delta} = utils:timing(fun() -> tally:tally(Tab, SubtyConstrs) end),
    case Res of
        {error, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            false;
        Substs ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            ?LOG_TRACE("Substitutions:~n~s", [pretty:render_substs(Substs)]),
            Substs
    end.
