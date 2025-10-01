-module(constr_error_locs).

-export([
    simp_constrs_to_blocks/1
]).

-export_type([
    constr_error_kind/0,
    constr_blocks/0,
    constr_block/0
]).

-type constr_error_kind() :: tyerror | redundant_branch | non_exhaustive_case.

-type constr_blocks() :: list(constr_block()).

-type constr_block() :: {constr_error_kind(), ast:loc(), string(), constr:subty_constrs()}.

-spec loc_of_block(constr_block()) -> ast:loc().
loc_of_block({_, L, _, _}) -> L.

-spec simp_constrs_to_blocks(constr:simp_constrs()) -> constr_blocks().
simp_constrs_to_blocks(Ds) ->
    % ListOfBlocks is a list of list of simp_constr_block().
    % The inner list has a meaningful ordering (namely by the structure of the program).
    % The outer list is randomly sorted (given by the order of sets:to_list(Ds)).
    ListOfBlocks = lists:map(fun simp_constr_to_blocks/1, sets:to_list(Ds)),
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
    lists:append(SortedListOfBlocks).

-spec simp_constr_to_blocks(constr:simp_constr()) -> constr_blocks().
simp_constr_to_blocks(D) ->
    case D of
        {scsubty, L, _, _} -> [{tyerror, L, "subty", utils:single(D)}];
        {scmater, _L, _T, _Alpha} -> [];
        {sccase, {_LocScrut, DsScrut}, {LocExhaus, DsExhaust}, Branches} ->
            BranchBlocks =
                utils:concat_map(Branches,
                    fun ({sccase_branch, {LocGuard, Guards}, _Cond,
                            {LocBody, Body}, {LocResult, Result}}) ->
                        BodyBlocks =
                            case sets:size(Body) of
                                1 -> simp_constr_to_blocks(lists:nth(1, sets:to_list(Body)));
                                _ -> [{tyerror, LocBody, "branch body",
                                        constr_collect:collect_constrs_no_matching_cond(Body)}]
                            end,
                        GuardBlocks =
                            case sets:is_empty(Guards) of
                                true -> [];
                                false ->
                                    [{tyerror, LocGuard, "branch guard",
                                         constr_collect:collect_constrs_no_matching_cond(Guards)}]
                            end,
                        ResultBlocks =
                            [{tyerror, LocResult, "branch result",
                                constr_collect:collect_constrs_no_matching_cond(Result)}],
                        GuardBlocks ++ ResultBlocks ++ BodyBlocks
                    end),
            simp_constrs_to_blocks(DsScrut) ++
                [{non_exhaustive_case, LocExhaus, "case exhaust",
                    constr_collect:collect_constrs_no_matching_cond(DsExhaust)}] ++
                BranchBlocks
    end.
