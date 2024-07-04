-module(constr_collect).

-include_lib("log.hrl").

-export([
    collect_constrs_no_matching_cond/1,
    collect_matching_cond_constrs/1
]).

-export_type([
]).

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

