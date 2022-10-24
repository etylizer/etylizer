-module(attr).

% @doc Parser for -ety attributes

-export([
    ety_attrs_from_file/1
    ]).

-include_lib("eunit/include/eunit.hrl").

-type ety_attr() :: {ety, ast:loc(), term()}.

-spec ety_attrs_from_file(file:filename()) -> t:opt([ety_attr()], string()).
ety_attrs_from_file(Path) ->
    case utils:file_get_lines(Path) of
        {ok, Lines} -> ety_attrs_from_lines(Path, Lines);
        {error, Why} -> {error, utils:sformat("Error reading file ~s: ~1000p", Path, Why)}
    end.

-spec ety_attrs_from_lines(string(), [string()]) -> t:opt([ety_attr()], string()).
ety_attrs_from_lines(Path, Lines) -> ety_attrs_from_lines(Path, 1, Lines).

-spec ety_attrs_from_lines(string(), t:lineno(), [string()]) -> t:opt([ety_attr()], string()).
ety_attrs_from_lines(Path, Lineno, Lines) ->
    Loop =
        fun Loop(N, List) ->
            case List of
                [] -> [];
                [Line | RestLines] ->
                    Rest = Loop(N + 1, RestLines),
                    case parse_ety_attr({loc, Path, N, 1}, Line) of
                        no_attr -> Rest;
                        {ok, R} -> [R | Rest]
                    end
            end
        end,
    try {ok, Loop(Lineno, Lines)}
    catch {bad_attr, Msg} -> {error, utils:sformat("~1000p", Msg)} end.

-spec parse_ety_attr(ast:loc(), string()) -> no_attr | {ok, ety_attr()}.
parse_ety_attr(Loc, S) ->
    {loc, _, N, _} = Loc,
    case S of
       "%-ety" ++ Rest ->
           case string:trim(Rest) of
               TermStr = ("(" ++ _) ->
                   case erl_scan:string(TermStr, N) of
                       {ok, Toks, _} ->
                           case erl_parse:parse_term(Toks) of
                               {ok, Term} -> {ok, {ety, Loc, Term}};
                               {error, E} -> throw({bad_attr, E})
                            end;
                        E -> throw({bad_attr, E})
                    end;
                _ -> throw({bad_attr, "Invalid ety attribute"})
            end;
        _ -> no_attr
    end.

-spec parse_ety_attr_test() -> ok.
parse_ety_attr_test() ->
    Loc = {loc, "foo.erl", 2, 3},
    ?assertEqual({ok, {ety, Loc, 1}}, parse_ety_attr(Loc, "%-ety(1).")),
    ?assertEqual({ok, {ety, Loc, {foo, bar}}}, parse_ety_attr(Loc, "%-ety({foo, bar}).")),
    ?assertEqual(no_attr, parse_ety_attr(Loc, "%-xx({foo, bar}).")).
