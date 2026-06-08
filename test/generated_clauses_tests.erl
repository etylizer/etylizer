-module(generated_clauses_tests).

% Compiler-generated case clauses ({generated, true} in their annotation) are exempt from
% the redundancy check. Hand-written clauses are still checked, even at the same position
% as a generated clause (see ast:generator()).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

% The `false` branches can never match
-define(SRC,
    "-module(generated_clauses).\n"
    "-spec f(true) -> atom().\n"
    "f(X) -> case X of true -> a; false -> b; false -> c end.\n").

redundant_clause_test() ->
    ?assertEqual(redundant, check(fun(Cs) -> Cs end)).

generated_clauses_test() ->
    ?assertEqual(ok, check(fun([T, B, C]) -> [T, generated(B), generated(C)] end)).

% The match in the `false` branch can never match
-define(SRC_MATCH,
    "-module(generated_clauses).\n"
    "-spec f(true) -> atom().\n"
    "f(X) -> case X of true -> a; false -> ok = X end.\n").

% A generated match is exempt as well, although the match rewrite builds its clause
generated_match_test() ->
    ?assertEqual(redundant, check(?SRC_MATCH, fun([T, F]) -> [T, generated(F)] end)),
    ?assertEqual(ok, check(?SRC_MATCH, fun([T, F]) -> [T, all_generated(F)] end)).

% A hand-written clause that shares its location with a generated clause is still checked
same_location_test() ->
    ?assertEqual(redundant,
                 check(fun([T, B, C]) -> [T, generated(B), setelement(2, C, element(2, B))] end)).

% The compiler's marker is kept in the location of the transformed clause
generated_loc_test() ->
    Forms = ast_transform:trans("generated_clauses.erl",
                                raw_forms(fun([T, B, C]) -> [T, generated(B), C] end)),
    Generators = utils:everything(
                   fun({case_clause, L, _, _, _}) -> {ok, ast:generated_by(L)};
                      (_) -> error
                   end, Forms),
    ?assertEqual([none, compiler, none], Generators).

check(MarkClauses) -> check(?SRC, MarkClauses).

% Type checks Src after applying MarkClauses to the clauses of its case expression.
check(Src, MarkClauses) ->
    Opts = #opts{},
    tmp:with_tmp_dir("generated_clauses", "root", delete, fun(Dir) ->
        Path = filename:join(Dir, "generated_clauses.erl"),
        ok = file:write_file(Path, Src),
        parse_cache:with_cache(Opts, fun() -> global_state:with_new_state(fun() ->
            Forms = ast_transform:trans(Path, raw_forms(Src, MarkClauses)),
            Tab = symtab:std_symtab(paths:compute_search_path(Opts), symtab:empty(), Opts#opts.gradual_typing_mode),
            Ctx = typing:new_ctx(Tab, symtab:empty(), error),
            try
                typing:check_forms(Ctx, Path, Forms, sets:new(), sets:new(), false),
                ok
            catch
                throw:{etylizer, ty_error, Msg} ->
                    case string:find(Msg, "this branch never matches") of
                        nomatch -> {error, Msg};
                        _ -> redundant
                    end
            end
        end) end)
    end).

raw_forms(MarkClauses) -> raw_forms(?SRC, MarkClauses).

raw_forms(Src, MarkClauses) ->
    {ok, Tokens, _} = erl_scan:string(Src, {1, 1}),
    [mark_case_clauses(MarkClauses, Form) || Form <- parse_forms(Tokens)].

parse_forms([]) -> [];
parse_forms(Tokens) ->
    {FormTokens, [Dot | Rest]} = lists:splitwith(fun(T) -> element(1, T) =/= dot end, Tokens),
    {ok, Form} = erl_parse:parse_form(FormTokens ++ [Dot]),
    [Form | parse_forms(Rest)].

mark_case_clauses(MarkClauses, {'case', Anno, E, Clauses}) ->
    {'case', Anno, E, MarkClauses(Clauses)};
mark_case_clauses(MarkClauses, T) when is_tuple(T) ->
    list_to_tuple(mark_case_clauses(MarkClauses, tuple_to_list(T)));
mark_case_clauses(MarkClauses, L) when is_list(L) ->
    [mark_case_clauses(MarkClauses, X) || X <- L];
mark_case_clauses(_, X) -> X.

generated(Clause) ->
    setelement(2, Clause, erl_anno:set_generated(true, element(2, Clause))).

% Like generated/1, but for everything in the clause
all_generated(Clause) ->
    erl_parse:map_anno(fun(Anno) -> erl_anno:set_generated(true, Anno) end, Clause).
