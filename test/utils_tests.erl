-module(utils_tests).

-include_lib("eunit/include/eunit.hrl").

hash_sha1_test() ->
    Bin = list_to_binary("Hello World\n"),
    Hash = utils:hash_sha1(Bin),
    ?assertEqual("648A6A6FFFFDAA0BADB23B8BAF90B6168DD16B3A", Hash).

% the generic traversals are also tested with improper lists
-dialyzer({no_improper_lists, [everything_test/0]}).

everywhere_typed_test() ->
    Descend = fun(F, {node, L, R}) -> {node, F(L), F(R)}; (_, Leaf) -> Leaf end,
    Double = fun({leaf, N}) -> {ok, {leaf, 2 * N}}; (_) -> error end,
    ?assertEqual({node, {leaf, 2}, {node, {leaf, 4}, {leaf, 6}}},
                 utils:everywhere(Descend, Double, {node, {leaf, 1}, {node, {leaf, 2}, {leaf, 3}}})).

everything_test() ->
    Ints = fun(X) when is_integer(X) -> {ok, X}; (_) -> error end,
    ?assertEqual([1, 2, 3, 4, 5], utils:everything(Ints, {a, [1, 2 | 3], {4, [], "", {5}}})),
    ?assertEqual([1, 2], lists:sort(utils:everything(Ints, #{1 => a, b => [2]}))),
    % {ok, X} does not traverse the term, {rec, X} does
    Pairs = fun(Res) -> fun({p, _, _} = P) -> {Res, P}; (_) -> error end end,
    T = {p, {p, a, b}, c},
    ?assertEqual([T], utils:everything(Pairs(ok), T)),
    ?assertEqual([T, {p, a, b}], utils:everything(Pairs(rec), T)).

everything_typed_test() ->
    Children = fun({node, L, R}) -> [L, R]; (_) -> [] end,
    Leaves = fun({leaf, N}) -> {ok, N}; (_) -> error end,
    ?assertEqual([1, 2, 3],
                 utils:everything(Children, Leaves, [{node, {leaf, 1}, {node, {leaf, 2}, {leaf, 3}}}])).
