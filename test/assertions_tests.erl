-module(assertions_tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

% each test runs the checker from scratch
-define(_timeout(E), {timeout, 60, fun() -> E end}).

-define(DIR, "test_files/assertions/").

-spec check(string(), undefined | string()) -> ok | {fail, string()}.
check(File, Assertions) ->
    Opts = #opts{
        files = [?DIR ++ File],
        project_root = ?DIR,
        force = true,
        assertions = case Assertions of undefined -> undefined; _ -> ?DIR ++ Assertions end
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

none_test_() ->
    ?_timeout(fails_with("in first/1, not all cases are covered", check("asserted.erl", undefined))).

all_test_() ->
    ?_timeout(?assertEqual(ok, check("asserted.erl", "all.assertions"))).

wrong_type_test_() ->
    ?_timeout(fails_with("in int/1", check("asserted.erl", "wrong_type.assertions"))).

% without the hash, the error lists what starts at the position; a macro puts several
% expressions at the position of its argument
no_hash_test_() ->
    ?_timeout(begin
        fails_with("asserted.erl:18:16: assert_type needs the hash of an expression that starts here: "
                   "`1` (64fd3c), `X` (ed0a1f), `X + 1` (cbd9cf)",
                   check("asserted.erl", "no_hash.assertions"))
    end).

% the hash of the match of line 11 at a position that holds another expression
moved_test_() ->
    ?_timeout(fails_with("asserted.erl:12:5: assert_pattern needs the hash of an expression that starts here: `X` (ed0a1f)",
                         check("asserted.erl", "moved.assertions"))).

no_expression_test_() ->
    ?_timeout(fails_with("asserted.erl:11:1: assert_type needs the hash of an expression that starts here: none",
                         check("asserted.erl", "nothing.assertions"))).

% an assertion that is not needed leaves a branch that never matches
unneeded_test_() ->
    ?_timeout(begin
        ?assertEqual(ok, check("unneeded.erl", undefined)),
        fails_with("in first/1, this branch never matches", check("unneeded.erl", "unneeded.assertions"))
    end).
