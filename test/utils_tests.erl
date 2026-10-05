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
-dialyzer({no_improper_lists, [everything_test/0]}).

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
