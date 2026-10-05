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

% The right-hand sides of all specs and type declarations, with their type schemes.
ty_schemes(Forms) ->
    [TyScm || {attribute, _, spec, _, _, TyScm, _} <- Forms]
        ++ [TyScm || {attribute, _, type, _, {_, TyScm}} <- Forms].

%% Reference implementations based on the generic traversals

old_loc_replacer(X) ->
    case ast:is_loc(X) of
        true -> {ok, {loc, "", 0, 0}};
        false -> error
    end.

old_remove_locs(X) -> utils:everywhere(fun old_loc_replacer/1, X).

old_referenced_modules_via_types(Forms) ->
    lists:uniq(utils:everything(
        fun({attribute, _, import, {ModuleName, _}}) when is_atom(ModuleName) -> {ok, ModuleName};
           ({ty_qref, ModuleName, _, _}) when is_atom(ModuleName) -> {ok, ModuleName};
           (_) -> error
        end, Forms)).

old_referenced_modules(Forms) ->
    lists:uniq(utils:everything(
        fun({attribute, _, import, {ModuleName, _}}) when is_atom(ModuleName) -> {ok, ModuleName};
           ({qref, ModuleName, _, _}) when is_atom(ModuleName) -> {ok, ModuleName};
           ({ty_qref, ModuleName, _, _}) when is_atom(ModuleName) -> {ok, ModuleName};
           (_) -> error
        end, Forms)).

old_replace_dynamic(Ty) ->
    Counter = counters:new(1, []),
    utils:everywhere(
        fun({predef, dynamic}) ->
                counters:add(Counter, 1, 1),
                {ok, {var, list_to_atom(utils:sformat("%~w", counters:get(Counter, 1)))}};
           (_) -> error
        end, Ty).

old_discriminate_framevars(Ty) ->
    utils:everywhere(
        fun({var, N}) when is_atom(N) ->
                case atom_to_list(N) of
                    [$% | _] -> {ok, {predef, dynamic}};
                    _ -> error
                end;
           (_) -> error
        end, Ty).

old_replace_locs(Term) ->
    utils:everywhere(
        fun(X) ->
            case ast:is_loc(X) of
                true -> {ok, {internal, ty_parser}};
                false -> error
            end
        end, Term).

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

remove_locs_test_() ->
    {timeout, 300, fun() ->
        for_all_files(fun(File, Forms) ->
            ?assertEqual({File, old_remove_locs(Forms)}, {File, ast_utils:remove_locs(Forms)})
        end)
    end}.

map_locs_test_() ->
    {timeout, 300, fun() ->
        for_all_files(fun(File, Forms) ->
            Old = utils:everywhere(
                fun({loc, F, L, C}) when F =:= File -> {ok, {loc, "other", L, C}};
                   (_) -> error
                end, Forms),
            New = ast_traverse:map_locs_forms(
                fun Rename({loc, F, L, C}) when F =:= File -> {loc, "other", L, C};
                    Rename({generated, G, From}) -> {generated, G, Rename(From)};
                    Rename(Loc) -> Loc
                end, Forms),
            ?assertEqual({File, Old}, {File, New})
        end)
    end}.

referenced_modules_test_() ->
    {timeout, 300, fun() ->
        for_all_files(fun(File, Forms) ->
            ?assertEqual({File, old_referenced_modules(Forms)},
                         {File, ast_utils:referenced_modules(Forms)}),
            ?assertEqual({File, old_referenced_modules_via_types(Forms)},
                         {File, ast_utils:referenced_modules_via_types(Forms)})
        end)
    end}.

types_test_() ->
    {timeout, 300, fun() ->
        for_all_files(fun(File, Forms) ->
            lists:foreach(
                fun(TyScm = {ty_scheme, _, Ty}) ->
                    ?assertEqual({File, old_replace_locs(TyScm)}, {File, ty_parser:replace_locs(TyScm)}),
                    ?assertEqual({File, old_replace_locs(Ty)}, {File, ty_parser:replace_locs(Ty)}),
                    % make sure that there is something to replace
                    Gradual = {union, [Ty, {predef, dynamic}, {tuple, [{predef, dynamic}, Ty]}]},
                    Framed = gradual_utils:replace_dynamic(Gradual, gradual_utils:new_ctx()),
                    ?assertEqual({File, old_replace_dynamic(Gradual)}, {File, Framed}),
                    ?assertEqual({File, old_discriminate_framevars(Framed)},
                                 {File, gradual_utils:discriminate_framevars(Framed)})
                end, ty_schemes(Forms))
        end)
    end}.

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
