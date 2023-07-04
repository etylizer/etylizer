-module(parse_cache).

-include_lib("log.hrl").
-include_lib("parse.hrl").
-include_lib("ety_main.hrl").

-export([init/1, cleanup/0, parse/2]).
-export_type([file_kind/0]).

-spec init(#opts{}) -> ok.
init(Opts) ->
    ets:new(forms_table, [set, named_table, {keypos, 1}]),
    ets:insert(forms_table, {opts, Opts}). % special entry

-spec cleanup() -> ok.
cleanup() ->
    ets:delete(forms_table),
    ok.

-type file_kind() :: intern | {extern, [file:filename()]}.

-spec parse(file_kind, file:filename()) -> [ast:form()].
parse(Kind, Path) ->
    PathNorm = filename:nativename(Path),
    case ets:lookup(forms_table, PathNorm) of
        [{_, {StoredKind, Forms}}] ->
            if Kind =:= StoredKind -> ok;
                true ->
                    ?ABORT("Previously parsed ~p with kind ~p, now requested for kind ~p",
                        PathNorm, StoredKind, Kind)
            end,
            ?LOG_DEBUG("Retrieving parse result for ~p from cache", PathNorm),
            Forms;
        [] ->
            [{_, Opts}] = ets:lookup(forms_table, opts),
            Forms = really_parse_file(Kind, PathNorm, Opts),
            ets:insert(forms_table, {PathNorm, {Kind, Forms}}),
            Forms;
        X -> ?ABORT("Unexpected entry in parse cache for key ~p: ~p", PathNorm, X)
    end.

-spec really_parse_file(file_kind(), file:filename(), #opts{}) -> [ast:form()].
really_parse_file(Kind, File, Opts) ->
    ?LOG_INFO("Really parsing ~s ...", File),
    ParseOpts =
        case Kind of
            intern -> #parse_opts{
                        includes = Opts#opts.includes,
                        defines = Opts#opts.defines
                    };
            {extern, Includes} ->
                #parse_opts{ verbose = false, includes = Includes }
        end,
    RawForms = parse:parse_file_or_die(File, ParseOpts),
    if  Opts#opts.dump_raw -> ?LOG_NOTE("Raw forms in ~s:~n~p", File, RawForms);
        true -> ok
    end,
    ?LOG_TRACE("Parse result (raw):~n~120p", RawForms),

    if Opts#opts.sanity ->
            ?LOG_INFO("Checking whether parse result conforms to AST in ast_erl.erl ..."),
            {RawSpec, _} = ast_check:parse_spec("src/ast_erl.erl"),
            case ast_check:check_against_type(RawSpec, ast_erl, forms, RawForms) of
                true ->
                    ?LOG_INFO("Parse result from ~s conforms to AST in ast_erl.erl", File);
                false ->
                    ?ABORT("Parse result from ~s violates AST in ast_erl.erl", File)
            end;
       true -> ok
    end,

    ?LOG_DEBUG("Transforming ~s ...", File),
    Forms = ast_transform:trans(File, RawForms),
    if  Opts#opts.dump ->
            ?LOG_NOTE("Transformed forms in ~s:~n~p", File, ast_utils:remove_locs(Forms));
        true -> ok
    end,
    ?LOG_TRACE("Parse result (after transform):~n~120p", Forms),
    Forms.
