-module(parse).

% @doc This module provides functionality for parsing the erlang source code.
% It returns an AST matching the types in the ast module.

-include("log.hrl").
-include("parse.hrl").

-export([
    parse_file/2,
    parse_file_or_die/1,
    parse_file_or_die/2,
    parse_transform/2
]).

-include("etylizer.hrl").

-define(TABLE, parse_result).
-define(FORMS, forms).


% Scanner: http://erlang.org/doc/man/erl_parse.html
% Parser: http://erlang.org/doc/man/erl_parse.html
% Compile: https://erlang.org/doc/man/compile.html

-spec parse_file(string(), parse_opts()) -> error | {ok, [ast_erl:form()]}.
parse_file(Path, Opts) ->
    init_parse_table(),
    ?LOG_TRACE("Parsing ~s", Path),
    Ext = filename:extension(Path),
    if
        Ext == ".erl" ->
            do_parse_erl(Path, Opts);
        true ->
            ?LOG_ERROR("Invalid input file: ~s", Path),
            error
    end.

-spec init_parse_table() -> ok.
init_parse_table() ->
    case ets:whereis(?TABLE) of
        undefined ->
            ets:new(?TABLE, [named_table, public, set]),
            ok;
        _ ->
            ets:delete_all_objects(?TABLE),
            ok
    end.

-spec make_define_opt({atom(), string()}) -> {d, atom()} | {d, atom(), string()}.
make_define_opt({Name, Val}) ->
    case string:len(Val) of
        0 -> {d, Name};
        _ -> {d, Name, Val}
    end.

-spec build_compile_opts(parse_opts()) -> [compile:option()].
build_compile_opts(Opts) ->
    [{parse_transform,parse},basic_validation, report] ++
    (case Opts#parse_opts.verbose of true -> [verbose]; _ -> [] end) ++
    lists:map(fun (X) -> {i,X} end, Opts#parse_opts.includes) ++
    lists:map(fun make_define_opt/1, Opts#parse_opts.defines).

-spec do_parse_erl(string(), parse_opts()) -> error | {ok, [ast_erl:form()]}.
do_parse_erl(Path, Opts) ->
    NoExt = filename:rootname(Path),
    CompileOpts = build_compile_opts(Opts),
    case compile:file(NoExt, CompileOpts) of
        {ok, _} ->
            extract_parse_result(Path);
        error ->
            log_parse_error(Path);
        _ ->
            log_unexpected_compile(Path)
    end.

-spec log_parse_error(string()) -> error.
log_parse_error(Path) ->
    ?LOG_NOTE("Error parsing ~s", Path),
    error.

-spec log_unexpected_compile(string()) -> error.
log_unexpected_compile(Path) ->
    ?LOG_ERROR("Unexpected compile result for ~s", Path),
    error.

-spec extract_parse_result(string()) -> error | {ok, [ast_erl:form()]}.
extract_parse_result(Path) ->
    ?LOG_TRACE("Done parsing ~s", Path),
    case ets:lookup(?TABLE, ?FORMS) of
        [{_, StoredForms}] ->
            {ok, ?assert_type(StoredForms, [ast_erl:form()])};
        _ ->
            ?LOG_ERROR("No result in ETS table after parsing"),
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

-spec parse_transform(any(), any()) -> any().
parse_transform(Forms, _Opts) ->
    try
        ets:insert(?TABLE, {?FORMS, Forms}),
        Forms
    catch
        throw:E ->
            ?LOG_ERROR("Error throw in parse_transform: ~p", E),
            Forms;
        error:E ->
            ?LOG_ERROR("Error error in parse_transform: ~p", E),
            Forms;
        exit:E ->
            ?LOG_ERROR("Error exit in parse_transform: ~p", E),
            Forms
    end.
