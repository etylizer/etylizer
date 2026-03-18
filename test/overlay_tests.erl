-module(overlay_tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

% each test runs the checker from scratch
-define(_timeout(E), {timeout, 60, fun() -> E end}).

-define(DIR, "test_files/overlay/").

-spec check(string(), [string()]) -> ok | {fail, string()}.
check(File, Overlays) ->
    Opts = #opts{
        files = [?DIR ++ File],
        project_root = ?DIR,
        force = true,
        type_overlay = [?DIR ++ O || O <- Overlays]
    },
    try
        etylizer_main:doWork(Opts),
        ok
    catch
        throw:{etylizer, _, Msg}:_ -> {fail, lists:flatten(Msg)}
    end.

-spec fails_with(string(), ok | {fail, string()}) -> ok.
fails_with(Expected, Result) ->
    {fail, Msg} = Result,
    ?assertNotEqual(nomatch, string:find(Msg, Expected)).

% without a spec, inc/1 is dynamic
no_overlay_test_() ->
    ?_timeout(?assertEqual(ok, check("unspecced.erl", []))).

unspecced_function_test_() ->
    ?_timeout(fails_with("in use/0", check("unspecced.erl", ["spec_inc.erl"]))).

function_with_spec_test_() ->
    ?_timeout(fails_with("Overlay spec for unspecced:use/0", check("unspecced.erl", ["spec_use.erl"]))).

missing_function_test_() ->
    ?_timeout(fails_with("Overlay spec for unspecced:no_such_function/1", check("unspecced.erl", ["spec_missing.erl"]))).

several_overlays_test_() ->
    ?_timeout(begin
        fails_with("in rev/0", check("two_libs.erl", [])),
        fails_with("in last/0", check("two_libs.erl", ["lib_reverse.erl"])),
        fails_with("in rev/0", check("two_libs.erl", ["lib_last.erl"])),
        ?assertEqual(ok, check("two_libs.erl", ["lib_reverse.erl", "lib_last.erl"]))
    end).
