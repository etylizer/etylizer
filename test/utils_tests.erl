-module(utils_tests).

-include_lib("eunit/include/eunit.hrl").

hash_test() ->
    Bin = list_to_binary("Hello World\n"),
    Hash = utils:hash(Bin),
    % utils:hash/1 is an MD5 content fingerprint (see utils.erl): the browser
    % BEAM cannot load the OpenSSL-backed crypto NIF, so this is deliberately
    % not SHA-1.
    ?assertEqual("E59FF97941044F85DF5297E1C302D260", Hash).
