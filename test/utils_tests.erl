-module(utils_tests).

-include_lib("eunit/include/eunit.hrl").

hash_test() ->
    Bin = list_to_binary("Hello World\n"),
    Hash = utils:hash(Bin),
    % utils:hash/1 is an MD5 content fingerprint (see utils.erl): the browser
    % BEAM cannot load the OpenSSL-backed crypto NIF, so this is deliberately
    % not SHA-1.
    ?assertEqual("E59FF97941044F85DF5297E1C302D260", Hash).

% the generic traversals are also tested with improper lists
-dialyzer({no_improper_lists, [everywhere_test/0, everything_test/0]}).

everywhere_test() ->
    Inc = fun(X) when is_integer(X) -> {ok, X + 1}; (_) -> error end,
    ?assertEqual({a, [2, 3], #{b => 4, 5 => [6]}}, utils:everywhere(Inc, {a, [1, 2], #{b => 3, 4 => [5]}})),
    % improper lists are traversed as well
    ?assertEqual([2, 3 | 4], utils:everywhere(Inc, [1, 2 | 3])),
    % {ok, X} does not traverse X, {rec, X} does
    ?assertEqual({done, 1}, utils:everywhere(fun({todo, X}) -> {ok, {done, X}}; (X) -> Inc(X) end, {todo, 1})),
    ?assertEqual({done, 2}, utils:everywhere(fun({todo, X}) -> {rec, {done, X}}; (X) -> Inc(X) end, {todo, 1})).

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
