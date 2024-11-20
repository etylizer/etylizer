-module(constr_collect).

-export([
    collect_constrs_no_matching_cond/1,
    collect_matching_cond_constrs/1,
    cross_product/3,
    cross_product_binary/3,
    cross_union_with_locs/1,
    collect_constrs_all_combinations/1
]).

-export_type([
    all_combinations/0
]).

% Collect all constraints but ignore all branch matching condition constraints.
% Always return the body constraints for the branches.
-spec collect_constrs_no_matching_cond(constr:simp_constrs()) -> constr:subty_constrs().
collect_constrs_no_matching_cond(Ds) -> collect_constrs_no_matching_cond(Ds, sets:new([{version, 2}])).

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

-type all_combinations() :: [{sets:set(ast:loc()), constr:subty_constrs()}].

% Collects all possible combinations of constraints "branch taken" / "branch not taken".
% Each combination has attached the set of locations of branches not taken.
-spec collect_constrs_all_combinations(constr:simp_constrs()) -> all_combinations().
collect_constrs_all_combinations(Ds) ->
    cross_union_with_locs(lists:map(fun collect_constr_all_combinations/1, sets:to_list(Ds))).

-spec collect_constr_all_combinations(constr:simp_constr()) -> all_combinations().
collect_constr_all_combinations(D) ->
    case D of
        {scsubty, _, _, _} ->
            [{sets:new([{version, 2}]), utils:single(D)}];
        {sccase, {_, DsScrut}, {_, DsExhaust}, Branches} ->
            ScrutCombs = collect_constrs_all_combinations(DsScrut),
            ExhaustCombs = collect_constrs_all_combinations(DsExhaust),
            BranchesCombs = lists:map(fun collect_branch_all_combinations/1, Branches),
            cross_union_with_locs([ScrutCombs, ExhaustCombs] ++ BranchesCombs)
    end.

-spec collect_branch_all_combinations(constr:simp_constr_case_branch()) -> all_combinations().
collect_branch_all_combinations(B) ->
    case B of
        {sccase_branch, {_, Guards}, Cond, {_, Body}, {_, Result}} ->
            GuardsCombs = collect_constrs_all_combinations(Guards),
            BodyCombs = collect_constrs_all_combinations(Body),
            ResultCombs = collect_constrs_all_combinations(Result),
            case Cond of
                none -> cross_union_with_locs([GuardsCombs, BodyCombs, ResultCombs]);
                {LocCond, X} ->
                    CondCombs = collect_constrs_all_combinations(X),
                    add_loc(LocCond, cross_union_with_locs([GuardsCombs, CondCombs])) ++
                        cross_union_with_locs([GuardsCombs, BodyCombs, ResultCombs])
            end
    end.

-spec add_loc(ast:loc(), all_combinations()) -> all_combinations().
add_loc(Loc, List) ->
    lists:map(fun ({Locs, Set}) -> {sets:add_element(Loc, Locs), Set} end, List).

-spec cross_union_with_locs([all_combinations()]) -> all_combinations().
cross_union_with_locs(LL) ->
    cross_product(LL,
        fun({Locs1, Cs1}, {Locs2, Cs2}) -> {sets:union(Locs1, Locs2), sets:union(Cs1, Cs2)} end,
        [{sets:new([{version, 2}]), sets:new([{version, 2}])}]).

% cross_product([S1, ..., Sn], [T1, ..., Tm], F) computes the cross-product of
% the two lists, where F is used to combine Si and Tj.
% cross_product([S1, ..., Sn], [T1, ..., Tm]) =
% [F(S1, T1), ..., F(S1, Tm), F(S2, T1), ..., F(S2, Tm), ..., F(Sn, T1), ..., F(Sn, Tm)]
% Logically, we have (assuming F is conjunction)
% (S1 \/ S2 \/ ... \/ Sn) /\ (T1 \/ T2 \/ ... \/ Tm) =
% (S1 /\ T1) \/ (S1 /\ T2) \/ ... \/ (Sn /\ Tm)
-spec cross_product_binary([T], [T], fun((T, T) -> T)) -> [T].
cross_product_binary(Combs1, Combs2, F) ->
    lists:flatmap(
        fun(X1) ->
                lists:map(fun(X2) -> F(X1, X2) end, Combs2)
        end,
        Combs1).

% cross_product([L1, ..., Ln], F) computes the cross-product of all list of sets in L1, ..., Ln.
% cross_product([L1, ..., Ln], F) =
% cross_product(..., cross_product(cross_product(L1, L2, F), L3, F) ..., Ln, F)
% We have cross_product([L1]) = L1 and cross_product([]) = [{}]
% Logically, each Li is a disjunction and the list [L1, ..., Ln] is the conjunction
% L1 /\ L2 /\ ... /\ Ln
% and cross_product moves the disjunction outwards.
-spec cross_product([[T]], fun((T, T) -> T), [T]) -> [T].
cross_product(LL, F, Empty) ->
    lists:foldl(
        fun (L1, L2) -> cross_product_binary(L1, L2, F) end,
        Empty,
        LL).
