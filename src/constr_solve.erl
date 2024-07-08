-module(constr_solve).

-include_lib("log.hrl").

-export([
    check_simp_constrs/4,
    check_simp_constrs_return_unmatched/4,
    solve_simp_constrs/3
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
    {ok, Unmachted::constr:locs()} | {error, error() | none}.
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
    ?LOG_DEBUG("Checking constraints for satisfiability to type check ~s:~n~s",
        What, pretty:render_constr(SubtyConstrs)),
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
                                    ?LOG_DEBUG("Branch at ~s is redundant. Constraints: ~s",
                                        ast:format_loc(Loc),
                                        pretty:render_constr(UnmatchedConstrs)),
                                    {error, {redundant_branch, Loc, ""}};
                                false ->
                                    ?LOG_DEBUG("Branch at ~s is not redundant. Constraints: ~s",
                                        ast:format_loc(Loc),
                                        pretty:render_constr(UnmatchedConstrs)),
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
            locate_tyerror(Tab, FixedTyvars, Blocks, sets:new())
    end.


-spec locate_tyerror(symtab:t(), sets:set(ast:ty_varname()), constr_error_locs:constr_blocks(),
    constr:subty_constrs()) -> ok | {error, error() | none}.
locate_tyerror(_Tab, _FreeSet, [], _DsAcc) -> {error, none};
locate_tyerror(Tab, FreeSet, [{Kind, Loc, _What, Ds} | Blocks], DsAcc) ->
    FullDs = sets:union(Ds, DsAcc),
    case is_satisfiable(Tab, FullDs, FreeSet, "error location") of
        false -> {error, {Kind, Loc, ""}};
        true -> locate_tyerror(Tab, FreeSet, Blocks, FullDs)
    end.

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
