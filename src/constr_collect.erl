-module(constr_collect).

-include_lib("log.hrl").

-export([
    collect_constrs_no_matching_cond/1,
    collect_matching_cond_constrs/1,
    cross_union/1,
    cross_union/2,
    collect_constrs_all_combinations/1
]).

-export_type([
]).

% Collect all constraints but ignore all branch matching condition constraints.
% Always return the body constraints for the branches.
-spec collect_constrs_no_matching_cond(constr:simp_constrs()) -> constr:subty_constrs().
collect_constrs_no_matching_cond(Ds) -> collect_constrs_no_matching_cond(Ds, sets:new()).

-spec collect_constrs_no_matching_cond(constr:simp_constrs(), constr:subty_constrs())
    -> constr:subty_constrs().
collect_constrs_no_matching_cond(Ds, OuterAcc) ->
    lists:foldl(
        fun (D, InnerAcc1) ->
            case D of
                {scsubty, _, _, _} -> sets:add_element(D, InnerAcc1);
                {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
                    lists:foldl(
                        fun ({sccase_branch, {_, Guards}, _Cond, {_, Body}, {_, Result}}, InnerAcc2) ->
                            collect_constrs_no_matching_cond(Result,
                                collect_constrs_no_matching_cond(Body,
                                    collect_constrs_no_matching_cond(Guards, InnerAcc2)))
                        end,
                        collect_constrs_no_matching_cond(DsScrut,
                            collect_constrs_no_matching_cond(DsExhaust, InnerAcc1)),
                        Branches)
            end
        end,
        OuterAcc,
        sets:to_list(Ds)).

-spec collect_matching_cond_constrs(constr:simp_constrs()) -> list({ast:loc(), constr:subty_constrs()}).
collect_matching_cond_constrs(Ds) -> collect_matching_cond_constrs(Ds, []).

% Collect only the matching condition constraints.
-spec collect_matching_cond_constrs(constr:simp_constrs(), list({ast:loc(), constr:subty_constrs()}))
    -> list({ast:loc(), constr:subty_constrs()}).
collect_matching_cond_constrs(Ds, OuterAcc) ->
    lists:reverse(lists:foldl(
        fun (D, InnerAcc1) ->
            case D of
                {scsubty, _, _, _} -> InnerAcc1;
                {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
                    lists:foldl(
                        fun ({sccase_branch, {_, Guards}, Cond, {_, Body}, {_, Result}}, InnerAcc2) ->
                            L = collect_matching_cond_constrs(Result,
                                    collect_matching_cond_constrs(Body,
                                        collect_matching_cond_constrs(Guards, InnerAcc2))),
                            case Cond of
                                none -> L;
                                {Loc, Ds2} ->
                                    [{Loc, collect_constrs_no_matching_cond(Ds2)} | L]
                            end
                        end,
                        collect_matching_cond_constrs(DsScrut,
                            collect_matching_cond_constrs(DsExhaust, InnerAcc1)),
                        Branches)
            end
        end,
        OuterAcc,
        sets:to_list(Ds))).

% empty disjunction: False
% empty conjunction: True
% collect_constrs_all_combinations({}) = [{}]
% cross_union([])
-spec collect_constrs_all_combinations(constr:simp_constrs()) -> [constr:subty_constrs()].
collect_constrs_all_combinations(Ds) ->
    cross_union(lists:map(fun collect_constr_all_combinations/1, sets:to_list(Ds))).

-spec collect_constr_all_combinations(constr:simp_constrs()) -> [constr:subty_constrs()].
collect_constr_all_combinations(D) ->
    case D of
        {scsubty, _, _, _} -> [utils:single(D)];
        {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
            ScrutCombs = collect_constrs_all_combinations(DsScrut),
            ExhaustCombs = collect_constrs_all_combinations(DsExhaust),
            BranchesCombs = lists:map(fun collect_branch_all_combinations/1, Branches),
            cross_union([ScrutCombs, ExhaustCombs] ++ BranchesCombs)
    end.

-spec collect_branch_all_combinations(constr:simp_constr_case_branch()) -> [constr:subty_constrs()].
collect_branch_all_combinations(B) ->
    case B of
        {sccase_branch, {_, Guards}, Cond, {_, Body}, {_, Result}} ->
            GuardsCombs = collect_constrs_all_combinations(Guards),
            BodyCombs = collect_constrs_all_combinations(Body),
            ResultCombs = collect_constrs_all_combinations(Result),
            case Cond of
                none -> cross_union([GuardsCombs, BodyCombs, ResultCombs]);
                {_, X} ->
                    CondCombs = collect_constrs_all_combinations(X),
                    cross_union([GuardsCombs, CondCombs]) ++
                        cross_union([GuardsCombs, BodyCombs, ResultCombs])
            end
    end.

% cross_union([S1, ..., Sn], [T1, ..., Tm]) computes the cross-product of
% the two lists, where union is used to combine Si and Tj.
% cross_union([S1, ..., Sn], [T1, ..., Tm]) =
% [S1 union T1, ..., S1 union Tm, S2 union T1, ..., S2 union Tm, ..., Sn union T1, ..., Sn union Tm]
-spec cross_union([sets:set(T)], [sets:set(T)]) -> [sets:set(T)].
cross_union(Combs1, Combs2) ->
    lists:flatmap(
        fun(S1) ->
                lists:map(fun(S2) -> sets:union(S1, S2) end, Combs2)
        end,
        Combs1).

% cross_union([L1, ..., Ln]) computes the cross-union of all list of sets in L1, ..., Ln.
% cross_union([L1, ..., Ln]) =
% cross_union(..., cross_union(cross_union(L1, L2), L3) ..., Ln)
% We have cross_union([L1]) = L1 and cross_union([]) = [{}]
-spec cross_union([[sets:set(T)]]) -> [sets:set(T)].
cross_union(L) ->
    lists:foldl(
        fun cross_union/2,
        [sets:new()],
        L).
