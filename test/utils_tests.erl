-module(utils_tests).

-include_lib("eunit/include/eunit.hrl").

hash_sha1_test() ->
    Bin = list_to_binary("Hello World\n"),
    Hash = utils:hash_sha1(Bin),
    ?assertEqual("648A6A6FFFFDAA0BADB23B8BAF90B6168DD16B3A", Hash).

everything_typed_test() ->
    Children = fun({node, L, R}) -> [L, R]; (_) -> [] end,
    Leaves = fun({leaf, N}) -> {ok, N}; (_) -> error end,
    ?assertEqual([1, 2, 3],
                 utils:everything(Children, Leaves, [{node, {leaf, 1}, {node, {leaf, 2}, {leaf, 3}}}])).
