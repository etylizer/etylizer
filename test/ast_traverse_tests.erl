-module(ast_traverse_tests).

% The typed traversals of ast_traverse must agree with the generic term traversals of
% utils (everything/2, everywhere/2) that they replace. The tests run both on the
% sources of etylizer and on the type checker test files, and compare the results.

-include_lib("eunit/include/eunit.hrl").
-include("parse.hrl").

-define(INCLUDES, ["src", "include", "src/erlang_types", "src/erlang_types/dnf",
                   "src/erlang_types/utils"]).

-spec corpus() -> [file:filename()].
corpus() ->
    filelib:wildcard("src/*.erl")
        ++ filelib:wildcard("src/erlang_types/*.erl")
        ++ filelib:wildcard("test_files/tycheck_simple/*.erl").

-spec parse_to_internal(file:filename()) -> {ok, ast:forms()} | error.
parse_to_internal(File) ->
    try
        RawForms = parse:parse_file_or_die(File, #parse_opts{includes = ?INCLUDES}),
        {ok, ast_transform:trans(File, RawForms, full)}
    catch
        throw:{etylizer, _, _} -> error
    end.

% Runs the check on all files of the corpus that can be transformed to the internal AST.
-spec for_all_files(fun((file:filename(), ast:forms()) -> ok)) -> ok.
for_all_files(Check) ->
    Parsed = lists:filtermap(
        fun(File) ->
            case parse_to_internal(File) of
                {ok, Forms} -> {true, {File, Forms}};
                error -> false
            end
        end, corpus()),
    % make sure that the test does not pass because nothing could be parsed
    ?assert(length(Parsed) > 80),
    lists:foreach(fun({File, Forms}) -> Check(File, Forms) end, Parsed).

%% Tests

% The typed query visits the same subterms as the generic one, in the same order.
% The only exception are the options of compile attributes, which are arbitrary terms.
subterms_test_() ->
    {timeout, 300, fun() ->
        for_all_files(fun(File, AllForms) ->
            Forms = [F || F <- AllForms, element(3, F) =/= compile],
            All = fun(T) -> {rec, T} end,
            ?assert({File, utils:everything(All, Forms)} =:= {File, ast_traverse:everything(All, [Forms])})
        end)
    end}.

compile_attribute_test() ->
    Loc = {loc, "file.erl", 1, 2},
    Form = {attribute, Loc, compile, [{inline, [{f, 1}]}]},
    ?assertEqual([Form, attribute, Loc, loc, "file.erl", $f, $i, $l, $e, $., $e, $r, $l, 1, 2, compile],
                 ast_traverse:everything(fun(T) -> {rec, T} end, [Form])).

% The type variables of specs are collected with a traversal that knows the structure of
% the types of the Erlang AST. It must find the same variables as the generic traversal.
spec_tyvars_test_() ->
    {timeout, 300, fun() ->
        Specs = lists:flatmap(
            fun(File) ->
                try parse:parse_file_or_die(File, #parse_opts{includes = ?INCLUDES}) of
                    RawForms -> [FunTys || {attribute, _, Kind, {_, FunTys}} <- RawForms,
                                           Kind =:= spec orelse Kind =:= callback]
                catch
                    throw:{etylizer, _, _} -> []
                end
            end, corpus()),
        ?assert(length(Specs) > 1000),
        lists:foreach(
            fun(FunTys) ->
                Old = utils:everything(fun(V = {var, _, _}) -> {ok, V}; (_) -> error end, FunTys),
                ?assertEqual(Old, ast_transform:spec_tyvars(FunTys))
            end, Specs)
    end}.
