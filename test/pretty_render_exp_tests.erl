% Tests that pretty:render_exp handles all ast:exp() variants without crashing.
-module(pretty_render_exp_tests).

-include_lib("eunit/include/eunit.hrl").
-include("parse.hrl").

-define(INCLUDES, ["include", "src", "src/erlang_types", "src/erlang_types/dnf", "src/erlang_types/utils"]).

-spec render_all_src_functions_test_() -> term().
render_all_src_functions_test_() ->
    {timeout, 120, fun() ->
        Files = filelib:wildcard("src/*.erl") ++ filelib:wildcard("src/**/*.erl"),
        lists:foreach(fun render_file/1, Files)
    end}.

-spec render_file(string()) -> ok.
render_file(Path) ->
    case parse:parse_file(Path, #parse_opts{includes = ?INCLUDES}) of
        {ok, RawForms} ->
            Forms =
                try ast_transform:trans(Path, RawForms)
                catch _:_ -> []
                end,
            lists:foreach(
                fun({function, _, Name, Arity, Clauses}) ->
                    lists:foreach(
                        fun({fun_clause, _, Pats, Guards, Body}) ->
                            try
                                [pretty:render_exp(P, 0) || P <- Pats],
                                [pretty:render_exp(G, 0) || Guard <- Guards, G <- Guard],
                                [pretty:render_exp(E, 0) || E <- Body]
                            catch
                                C:R:Stack ->
                                    io:format(user,
                                        "CRASH in ~s ~w/~w:~n  ~p:~p~n  ~p~n",
                                        [Path, Name, Arity, C, R, hd(Stack)]),
                                    error({render_exp_crash, Path, Name, Arity, C, R})
                            end
                        end,
                        Clauses);
                   (_) -> ok
                end,
                Forms);
        error ->
            io:format(user, "SKIP (parse error): ~s~n", [Path]),
            ok
    end.
