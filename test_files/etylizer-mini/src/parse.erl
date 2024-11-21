-module(parse).

% @doc This module provides functionality for parsing the erlang source code.
% It returns an AST matching the types in the ast module.

-include("log.hrl").
-include("parse.hrl").

-export([parse_file/1, parse_file/2, parse_file_or_die/1, parse_file_or_die/2, parse_transform/2]).

-define(TABLE, parse_result).
-define(FORMS, forms).


% Scanner: http://erlang.org/doc/man/erl_parse.html
% Parser: http://erlang.org/doc/man/erl_parse.html
% Compile: https://erlang.org/doc/man/compile.html

-spec parse_file(string()) -> error | {ok, [ast_erl:form()]}.
parse_file(Path) -> parse_file(Path, #parse_opts{}).

-spec parse_file(string(), parse_opts()) -> error | {ok, [ast_erl:form()]}.
parse_file(Path, Opts) ->
    case ets:whereis(?TABLE) of
        undefined ->
            ets:new(?TABLE, [named_table, public, set]);
        _ -> ets:delete_all_objects(?TABLE)
    end,
    ?LOG_TRACE("Parsing ~s", Path),
    Ext = filename:extension(Path),
    if
        Ext == ".erl" ->
            NoExt = filename:rootname(Path),
            CompileOpts =
                [{parse_transform,parse},strong_validation, report] ++
                (if Opts#parse_opts.verbose -> [verbose]; true -> [] end) ++
                lists:map(fun (X) -> {i,X} end, Opts#parse_opts.includes) ++
                lists:map(fun ({Name, Val}) ->
                    case string:len(Val) of
                        0 -> {d, Name};
                        _ -> {d, Name, Val}
                    end
                end, Opts#parse_opts.defines),
            ?LOG_TRACE("Calling compile:file for ~s, options: ~200p", NoExt, CompileOpts),
            case compile:file(NoExt, CompileOpts) of
                {ok, _} ->
                    ?LOG_TRACE("Done parsing ~s", Path),
                    case ets:lookup(?TABLE, ?FORMS) of
                        [{?FORMS, Forms}] -> {ok, Forms};
                        _ ->
                            ?LOG_ERROR("No result in ETS table after parsing"),
                            error
                    end;
                error ->
                    ?LOG_NOTE("Error parsing ~s", Path),
                    error
            end;
        true ->
            ?LOG_ERROR("Invalid input file: ~s", Path),
            error
    end.

-spec parse_file_or_die(string()) -> [ast_erl:form()].
parse_file_or_die(Path) -> parse_file_or_die(Path, #parse_opts{}).

-spec parse_file_or_die(string(), parse_opts()) -> [ast_erl:form()].
parse_file_or_die(Path, Opts) ->
    case parse_file(Path, Opts) of
        {ok, Forms} -> Forms;
        error -> errors:parse_error(utils:sformat("Error parsing ~s", Path))
    end.

-spec parse_transform(any(), any()) -> ok.
parse_transform(Forms, _Opts) ->
    try
        % ?LOG_TRACE("Forms: ~p", [Forms]),
        ets:insert(?TABLE, {?FORMS, Forms}),
        % ?LOG_TRACE("done with parse_transform"),
        Forms
    catch
        K:E ->
            ?LOG_ERROR("Error ~p in parse_transform: ~p", K, E),
            Forms
    end.
