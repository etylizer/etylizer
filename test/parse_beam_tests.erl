-module(parse_beam_tests).

-include_lib("eunit/include/eunit.hrl").
-include("parse.hrl").

-define(MOD, "-module(mod).\n-export([f/1]).\n-spec f(integer()) -> integer().\nf(X) -> X + 1.\n").

% Compiles the source as mod.erl in a temporary directory and parses mod.beam.
-spec parse_compiled(string(), [compile:option()]) -> {ok, [ast_erl:form()]} | error.
parse_compiled(Source, CompileOpts) ->
    tmp:with_tmp_dir("parse_beam", "root", delete,
        fun(Dir) ->
            Erl = filename:join(Dir, "mod.erl"),
            ok = file:write_file(Erl, Source),
            {ok, mod} = compile:file(Erl, [{outdir, Dir} | CompileOpts]),
            parse:parse_file(filename:join(Dir, "mod.beam"), #parse_opts{})
        end).

debug_info_test() ->
    {ok, Forms} = parse_compiled(?MOD, [debug_info]),
    ?assertMatch([{function, _, f, 1, _}], [F || F = {function, _, _, _, _} <- Forms]),
    ?assertMatch([{attribute, _, spec, {{f, 1}, _}}], [S || S = {attribute, _, spec, _} <- Forms]).

no_debug_info_test() ->
    ?assertEqual(error, parse_compiled(?MOD, [])).

% the module that reads the chunk is not on the code path
missing_backend_test() ->
    ?assertEqual(error, parse_compiled(?MOD, [{debug_info, {no_such_backend, []}}])).
