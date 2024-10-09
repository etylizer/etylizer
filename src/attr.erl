-module(attr).

% @doc Parser for -etylizer attributes

-export([
    etylizer_attrs_from_file/1
    ]).

-include_lib("eunit/include/eunit.hrl").

-type etylizer_attr() :: {etylizer, ast:loc(), term()}.

-spec etylizer_attrs_from_file(file:filename()) -> t:opt([etylizer_attr()], string()).
etylizer_attrs_from_file(Path) ->
    case utils:file_get_lines(Path) of
        {ok, Lines} -> etylizer_attrs_from_lines(Path, Lines);
        {error, Why} -> {error, utils:sformat("Error reading file ~s: ~1000p", Path, Why)}
    end.

-spec etylizer_attrs_from_lines(string(), [string()]) -> t:opt([etylizer_attr()], string()).
etylizer_attrs_from_lines(Path, Lines) -> etylizer_attrs_from_lines(Path, 1, Lines).

-spec etylizer_attrs_from_lines(string(), t:lineno(), [string()]) -> t:opt([etylizer_attr()], string()).
etylizer_attrs_from_lines(Path, Lineno, Lines) ->
    Loop =
        fun Loop(N, List) ->
            case List of
                [] -> [];
                [Line | RestLines] ->
                    Rest = Loop(N + 1, RestLines),
                    case parse_etylizer_attr({loc, Path, N, 1}, Line) of
                        no_attr -> Rest;
                        {ok, R} -> [R | Rest]
                    end
            end
        end,
    try {ok, Loop(Lineno, Lines)}
    catch {bad_attr, Msg} -> {error, utils:sformat("~1000p", Msg)} end.

-spec parse_etylizer_attr(ast:loc(), string()) -> no_attr | {ok, etylizer_attr()}.
parse_etylizer_attr(Loc, S) ->
    {loc, _, N, _} = Loc,
    case S of
       "%-etylizer" ++ Rest ->
           case string:trim(Rest) of
               TermStr = ("(" ++ _) ->
                   case erl_scan:string(TermStr, N) of
                       {ok, Toks, _} ->
                           case erl_parse:parse_term(Toks) of
                               {ok, Term} -> {ok, {etylizer, Loc, Term}};
                               {error, E} -> throw({bad_attr, E})
                            end;
                        E -> throw({bad_attr, E})
                    end;
                _ -> throw({bad_attr, "Invalid etylizer attribute"})
            end;
        _ -> no_attr
    end.

-spec parse_etylizer_attr_test() -> ok.
parse_etylizer_attr_test() ->
    Loc = {loc, "foo.erl", 2, 3},
    ?assertEqual({ok, {etylizer, Loc, 1}}, parse_etylizer_attr(Loc, "%-etylizer(1).")),
    ?assertEqual({ok, {etylizer, Loc, {foo, bar}}}, parse_etylizer_attr(Loc, "%-etylizer({foo, bar}).")),
    ?assertEqual(no_attr, parse_etylizer_attr(Loc, "%-xx({foo, bar}).")).
