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

% The specs that parse_beam:default_arg_specs/1 adds to a module, as source text.
-spec added_specs(string()) -> [string()].
added_specs(Body) ->
    {ok, Forms} = parse_compiled("-module(mod).\n" ++ Body, [debug_info]),
    [lists:flatten(erl_pp:form(S)) || S <- parse_beam:default_arg_specs(Forms) -- Forms].

-define(PAD, "-spec pad(binary(), integer(), binary()) -> binary().\npad(S, _, _) -> S.\n").

default_arg_specs_test_() ->
    [
     % the default is the last, the middle, the first parameter
     ?_assertEqual(["-spec pad(binary(), integer()) -> binary().\n"],
        added_specs("-export([pad/2, pad/3]).\n" ?PAD "pad(A, B) -> pad(A, B, <<>>).\n")),
     ?_assertEqual(["-spec pad(binary(), binary()) -> binary().\n"],
        added_specs("-export([pad/2, pad/3]).\n" ?PAD "pad(A, B) -> pad(A, 2, B).\n")),
     ?_assertEqual(["-spec pad(integer(), binary()) -> binary().\n"],
        added_specs("-export([pad/2, pad/3]).\n" ?PAD "pad(A, B) -> pad(<<>>, A, B).\n")),
     % two defaults
     ?_assertEqual(["-spec pad(binary()) -> binary().\n", "-spec pad(binary(), integer()) -> binary().\n"],
        added_specs("-export([pad/1, pad/2, pad/3]).\n" ?PAD
                    "pad(A) -> pad(A, 2, <<>>).\npad(A, B) -> pad(A, B, <<>>).\n")),
     % every clause of the spec is reduced
     ?_assertEqual(["-spec g(a) -> x;\n       (b) -> y.\n"],
        added_specs("-export([g/1, g/2]).\n-spec g(a, 1) -> x; (b, 2) -> y.\ng(a, 1) -> x;\ng(b, 2) -> y.\n"
                    "g(A) -> g(A, 1).\n")),
     % no spec: not exported, has a spec, a parameter is not passed on or twice,
     % the called function has no spec or one with constraints
     ?_assertEqual([], added_specs("-export([pad/3, h/0]).\n" ?PAD "pad(A, B) -> pad(A, 2, B).\nh() -> pad(<<>>, <<>>).\n")),
     ?_assertEqual([], added_specs("-export([pad/2, pad/3]).\n" ?PAD
                                   "-spec pad(binary(), binary()) -> binary().\npad(A, B) -> pad(A, 2, B).\n")),
     ?_assertEqual([], added_specs("-export([pad/2, pad/3]).\n" ?PAD "pad(A, _) -> pad(A, 2, <<>>).\n")),
     ?_assertEqual([], added_specs("-export([pad/2, pad/3]).\n" ?PAD "pad(A, B) -> pad(A, byte_size(B), A).\n")),
     ?_assertEqual([], added_specs("-export([k/1, k/2]).\nk(A, _) -> A.\nk(A) -> k(A, 1).\n")),
     ?_assertEqual([], added_specs("-export([k/1, k/2]).\n-spec k(T, integer()) -> T when T :: atom().\n"
                                   "k(A, _) -> A.\nk(A) -> k(A, 1).\n"))
    ].

% only the forms of Elixir modules get these specs
erlang_wrapper_test() ->
    {ok, Forms} = parse_compiled("-module(mod).\n-export([pad/2, pad/3]).\n" ?PAD "pad(A, B) -> pad(A, 2, B).\n",
                                 [debug_info]),
    ?assertEqual([], [S || S = {attribute, _, spec, {{pad, 2}, _}} <- Forms]).
