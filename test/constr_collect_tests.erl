-module(constr_collect_tests).

-include_lib("eunit/include/eunit.hrl").

-import(prettypr, [text/1]).

-spec check_lists_for_eq(list(T), list(T)) -> ok.
check_lists_for_eq(ExpectedList, GivenList) ->
    case length(ExpectedList) =:= length(GivenList) of
        false ->
            io:format("Lists have different length. Expected length ~w, given length ~w",
                [length(ExpectedList), length(GivenList)]),
            io:format("Expected:~n~200p~n~nGiven:~n~200p", [ExpectedList, GivenList]),
            error(utils:sformat("Lists have different length. Expected length ~w, given length ~w",
                length(ExpectedList), length(GivenList)));
        true -> ok
    end,
    N = length(ExpectedList),
    lists:foreach(
        fun ({{I, Exp}, Given}) ->
            if
                is_list(Exp) andalso is_list(Given) -> check_lists_for_eq(Exp, Given);
                true ->
                    case Exp =:= Given of
                        true -> ok;
                        false ->
                            io:format("List element ~w/~w differs!~n", [I, N]),
                            io:format("Expected:~n~200p~n~nGiven:~n~200p", [Exp, Given]),
                            error(utils:sformat("List element ~w (of ~w) differs.", I, N))
                    end
            end
        end,
        lists:zip(utils:with_index(1, ExpectedList), GivenList)).

-spec norm_list_of_sets([sets:set(T)]) -> [[T]].
norm_list_of_sets(L) ->
    lists:sort(lists:map(fun (Set) -> lists:sort(sets:to_list(Set)) end, L)).

-spec assert_list_of_sets([sets:set(T)], [sets:set(T)]) -> ok.
assert_list_of_sets(Expected, L) ->
    ExpectedNormed = norm_list_of_sets(Expected),
    LNormed = norm_list_of_sets(L),
    check_lists_for_eq(ExpectedNormed, LNormed).

%TODO Needs fix due to imprecise types? 
% -spec norm_list_of_pair_sets([{sets:set(T), sets:set(U)}]) -> [[{T, U}]].
norm_list_of_pair_sets(L) ->
    lists:sort(lists:map(
        fun ({Set1, Set2}) ->
            {lists:sort(sets:to_list(Set1)), lists:sort(sets:to_list(Set2))}
        end, L)).

-spec assert_list_of_pair_sets([{sets:set(T), sets:set(U)}], [{sets:set(T), sets:set(U)}]) -> ok.
assert_list_of_pair_sets(Expected, L) ->
    ExpectedNormed = norm_list_of_pair_sets(Expected),
    LNormed = norm_list_of_pair_sets(L),
    check_lists_for_eq(ExpectedNormed, LNormed).

-spec cross_union([sets:set(T)], [sets:set(T)]) -> [sets:set(T)].
cross_union(L1, L2) -> constr_collect:cross_product_binary(L1, L2, fun sets:union/2).

-spec cross_union([[sets:set(T)]]) -> [sets:set(T)].
cross_union(LL) -> constr_collect:cross_product(LL, fun sets:union/2, [sets:new([{version, 2}])]).

cross_union_empty_test() ->
    L = cross_union([]),
    ?assertEqual([sets:new([{version, 2}])], L).

cross_union_empty2_test() ->
    L = cross_union([[]]),
    ?assertEqual([], L).

cross_union_empty3_test() ->
    L = cross_union([[], []]),
    ?assertEqual([], L).

cross_union_single_test() ->
    L = cross_union([mk_set(1, 2)], [mk_set(3, 4)]),
    assert_list_of_sets([mk_set([1, 2, 3, 4])], L).

cross_union_single2_test() ->
    L = cross_union([[mk_set(1, 2)]]),
    assert_list_of_sets([mk_set(1, 2)], L).

cross_union1_test() ->
    L = cross_union([mk_set(1, 2), mk_set(3, 4)], [mk_set(5, 6), mk_set(7, 8)]),
    Expected = [
        mk_set([1, 2, 5, 6]), mk_set([1, 2, 7, 8]), mk_set([3, 4, 5, 6]), mk_set([3, 4, 7, 8])
    ],
    assert_list_of_sets(Expected, L).

cross_union2_test() ->
    L = cross_union(
        [[mk_set(1, 2), mk_set(3, 4)],
         [mk_set(5, 6), mk_set(7, 8)],
         [mk_set([9]), mk_set([10])]]
    ),
    Expected = [
        mk_set([1, 2, 5, 6, 9]), mk_set([1, 2, 5, 6, 10]),
        mk_set([1, 2, 7, 8, 9]), mk_set([1, 2, 7, 8, 10]),
        mk_set([3, 4, 5, 6, 9]), mk_set([3, 4, 5, 6, 10]),
        mk_set([3, 4, 7, 8, 9]), mk_set([3, 4, 7, 8, 10])
    ],
    assert_list_of_sets(Expected, L).

-spec mk_loc(integer()) -> ast:loc().
mk_loc(I) -> {loc, "test", I, I}.

-spec mk_stc(integer(), integer()) -> constr:simp_constr_subty().
mk_stc(I1, I2) -> {scsubty, mk_loc(I1), {singleton, I1}, {singleton, I2}}.

-spec mk_set(list(T)) -> sets:set(T).
mk_set(L) when is_list(L) -> sets:from_list(L, [{version, 2}]).

-spec mk_set(T, T) -> sets:set(T).
mk_set(X, Y) -> sets:from_list([X, Y], [{version, 2}]).

-spec collect_constrs_all_combinations_mini_test() -> ok.
collect_constrs_all_combinations_mini_test() ->
    C =
        {sccase,
            {mk_loc(1), mk_set([mk_stc(1, 2)])},   % scrutiny
            {mk_loc(2), mk_set([mk_stc(3, 4)])}, % exhaustiveness
            [{sccase_branch,
                {mk_loc(3), sets:new([{version, 2}])}, % guards
                {mk_loc(4), mk_set([mk_stc(5, 6)])}, % cond
                {mk_loc(5), mk_set([mk_stc(7, 8)])}, % body
                {mk_loc(6), sets:new([{version, 2}])}}  % result
            ]},
    L = constr_collect:collect_constrs_all_combinations(sets:from_list([C], [{version, 2}])),
    ?assertEqual(2, length(L)),
    assert_list_of_pair_sets([
        % branch not taken
        {utils:single(mk_loc(4)),
            sets:from_list([mk_stc(1, 2), mk_stc(3, 4), mk_stc(5, 6)], [{version, 2}])},
        % branch taken
        {sets:new([{version, 2}]),
            sets:from_list([mk_stc(1, 2), mk_stc(3, 4), mk_stc(7, 8)], [{version, 2}])}
    ], L).

-spec mk_sccase(integer()) -> constr:simp_constr_case().
mk_sccase(I) ->
    Base = 100 * I,
    {sccase,
        {mk_loc(Base + 1), mk_set([mk_stc(Base + 3, Base + 4)])},   % scrutiny
        {mk_loc(Base + 2), mk_set([mk_stc(Base + 5, Base + 6)])},   % exhaustiveness
        [{sccase_branch,
            {mk_loc(Base + 3), mk_set([mk_stc(Base + 7, Base + 8)])},     % guards
            {mk_loc(Base + 4), mk_set([mk_stc(Base + 9, Base + 10)])},    % cond
            {mk_loc(Base + 5), mk_set([mk_stc(Base + 11, Base + 12)])},   % body
            {mk_loc(Base + 6), mk_set([mk_stc(Base + 13, Base + 14)])}},  % result
         {sccase_branch,
            {mk_loc(Base + 7), mk_set([mk_stc(Base + 15, Base + 16)])},   % guards
            {mk_loc(Base + 8), mk_set([mk_stc(Base + 17, Base + 18)])},   % cond
            {mk_loc(Base + 9), mk_set([mk_stc(Base + 19, Base + 20)])},   % body
            {mk_loc(Base + 10), mk_set([mk_stc(Base + 21, Base + 22)])}}  % result
        ]}.

-spec mk_sccase_combs(
    integer(),
    constr:simp_constr_subty() | {ast:loc(), constr:simp_constr_subty()} | none
) -> constr_collect:all_combinations().
mk_sccase_combs(I, Add) ->
    Base = 100 * I,
    {AddLoc, AddList} =
        case Add of
            none -> {sets:new([{version, 2}]), []};
            {Loc, X} -> {utils:single(Loc), [X]};
            X -> {sets:new([{version, 2}]), [X]}
        end,
    Always = AddList ++ [
        mk_stc(Base + 3, Base + 4),
        mk_stc(Base + 5, Base + 6),
        mk_stc(Base + 7, Base + 8),
        mk_stc(Base + 15, Base + 16)
    ],
    Comb_on_on = mk_set(Always ++ [mk_stc(Base + 9, Base + 10), mk_stc(Base + 17, Base + 18)]),
    Comb_on_off = mk_set(Always ++ [mk_stc(Base + 9, Base + 10),
        mk_stc(Base + 19, Base + 20), mk_stc(Base + 21, Base + 22)]),
    Comb_off_on = mk_set(Always ++ [mk_stc(Base + 11, Base + 12), mk_stc(Base + 13, Base + 14),
        mk_stc(Base + 15, Base + 16), mk_stc(Base + 17, Base + 18)]),
    Comb_off_off = mk_set(Always ++ [mk_stc(Base + 11, Base + 12), mk_stc(Base + 13, Base + 14),
        mk_stc(Base + 19, Base + 20), mk_stc(Base + 21, Base + 22)]),
    [{sets:union(AddLoc, sets:from_list([mk_loc(Base + 4), mk_loc(Base + 8)], [{version, 2}])), Comb_on_on},
      {sets:add_element(mk_loc(Base + 4), AddLoc), Comb_on_off},
      {sets:add_element(mk_loc(Base + 8), AddLoc), Comb_off_on},
      {AddLoc, Comb_off_off}].

collect_constrs_all_combinations_simple_test() ->
    C = mk_sccase(0),
    L = constr_collect:collect_constrs_all_combinations(sets:from_list([C], [{version, 2}])),
    ?assertEqual(4, length(L)),
    Expected = mk_sccase_combs(0, none),
    assert_list_of_pair_sets(Expected, L).

collect_constrs_all_combinations_test() ->
    C1 = mk_stc(1, 2),
    C2 = {sccase,
            {mk_loc(1), mk_set([mk_stc(3, 4), mk_sccase(1)])},   % scrutiny
            {mk_loc(2), mk_set([mk_stc(5, 6), mk_sccase(2)])}, % exhaustiveness
            [{sccase_branch,
                {mk_loc(3), mk_set([mk_sccase(3), mk_stc(7, 8)])}, % guards
                {mk_loc(4), mk_set([mk_sccase(4), mk_stc(9, 10)])}, % cond
                {mk_loc(5), mk_set([mk_sccase(5), mk_stc(11, 12)])}, % body
                {mk_loc(6), mk_set([mk_sccase(6), mk_stc(13, 14)])}  % result
            }]},
    L = constr_collect:collect_constrs_all_combinations(sets:from_list([C1, C2], [{version, 2}])),
    % ExpAlwaysCombs: [constr_collect:all_combinations()]
    ExpAlwaysCombs = [
        [{sets:new([{version, 2}]), mk_set([C1])}],
        mk_sccase_combs(1, mk_stc(3, 4)), % scrutiny
        mk_sccase_combs(2, mk_stc(5, 6)), % exhaustiveness
        mk_sccase_combs(3, mk_stc(7, 8))   % guards
    ],
    CondOn = constr_collect:cross_union_with_locs(
        ExpAlwaysCombs ++ [mk_sccase_combs(4, {mk_loc(4), mk_stc(9, 10)})]),
    CondOff = constr_collect:cross_union_with_locs(
        ExpAlwaysCombs ++ [mk_sccase_combs(5, mk_stc(11, 12)), mk_sccase_combs(6, mk_stc(13, 14))]),
    assert_list_of_pair_sets(CondOn ++ CondOff, L).
