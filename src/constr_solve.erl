-module(constr_solve).

-include_lib("log.hrl").

-export([
    check_simp_constrs/3,
    check_simp_constrs_return_unmatched/3,
    solve_simp_constrs/3
]).

-export_type([
    error/0,
    error_kind/0
]).

-type error_kind() :: tyerror | redundant_branch | non_exhaustive_case | unsatisfiable.
-type error() :: {error_kind(), ast:loc(), string()}.

% Ignores unmatched branches, just returns their locations.
-spec check_simp_constrs_return_unmatched(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs()) ->
    ok | {error, error() | none, Unmachted::constr:locs()}.
check_simp_constrs_return_unmatched(Tab, FixedTyvars, Ds) ->
    % FIXME: this implementation is wrong
    SubtyConstrs = collect_constrs_ignoring_unmatched(Ds),
    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
        true -> ok;
        false -> {error, none, []} % FIXME: error locations
    end.


% Treats unmatched branches as errors.
-spec check_simp_constrs(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs()) ->
    ok | {error, error() | none}.
check_simp_constrs(Tab, FixedTyvars, Ds) ->
    SubtyConstrs = collect_constrs_ignoring_unmatched(Ds),
    ?LOG_DEBUG("Checking constraints for satisfiability:~n~s", pretty:render_constr(SubtyConstrs)),
    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
        true ->
            % check for redundant branches
            ReduDs = collect_unmatched_constrs(Ds),
            ?LOG_DEBUG("Checking ~w branches for redundancy", length(ReduDs)),
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
            {error, none} % FIXME: error locations
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
    % FIXME: we should include the redundancy checks here?!
    SubtyConstrs = collect_constrs_ignoring_unmatched(Ds),
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

-spec collect_constrs_ignoring_unmatched(constr:simp_constrs()) -> constr:subty_constrs().
collect_constrs_ignoring_unmatched(Ds) -> collect_constrs_ignoring_unmatched(Ds, sets:new()).

-spec collect_constrs_ignoring_unmatched(constr:simp_constrs(), constr:subty_constrs())
    -> constr:subty_constrs().
collect_constrs_ignoring_unmatched(Ds, OuterAcc) ->
    lists:foldl(
        fun (D, InnerAcc1) ->
            case D of
                {scsubty, _, _, _} -> sets:add_element(D, InnerAcc1);
                {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
                    lists:foldl(
                        fun ({sccase_branch, {_, Guards}, _Cond, {_, Body}}, InnerAcc2) ->
                            collect_constrs_ignoring_unmatched(Body,
                                collect_constrs_ignoring_unmatched(Guards, InnerAcc2))
                        end,
                        collect_constrs_ignoring_unmatched(DsScrut,
                            collect_constrs_ignoring_unmatched(DsExhaust, InnerAcc1)),
                        Branches)
            end
        end,
        OuterAcc,
        sets:to_list(Ds)).

-spec collect_unmatched_constrs(constr:simp_constrs()) -> list({ast:loc(), constr:subty_constrs()}).
collect_unmatched_constrs(Ds) -> collect_unmatched_constrs(Ds, []).

-spec collect_unmatched_constrs(constr:simp_constrs(), list({ast:loc(), constr:subty_constrs()}))
    -> list({ast:loc(), constr:subty_constrs()}).
collect_unmatched_constrs(Ds, OuterAcc) ->
    lists:reverse(lists:foldl(
        fun (D, InnerAcc1) ->
            case D of
                {scsubty, _, _, _} -> InnerAcc1;
                {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
                    lists:foldl(
                        fun ({sccase_branch, {_, Guards}, Cond, {_, Body}}, InnerAcc2) ->
                            L = collect_unmatched_constrs(Body,
                                    collect_unmatched_constrs(Guards, InnerAcc2)),
                            case Cond of
                                none -> L;
                                {Loc, Ds2} ->
                                    [{Loc, collect_constrs_ignoring_unmatched(Ds2)} | L]
                            end
                        end,
                        collect_unmatched_constrs(DsScrut,
                            collect_unmatched_constrs(DsExhaust, InnerAcc1)),
                        Branches)
            end
        end,
        OuterAcc,
        sets:to_list(Ds))).

