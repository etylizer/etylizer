-module(parse_cache).

-include("log.hrl").
-include("parse.hrl").
-include("ety_main.hrl").

-export([init/1, cleanup/0, parse/2]).
-export_type([file_kind/0]).

-define(TABLE, forms_table).

-spec init(#opts{}) -> ok.
init(Opts) ->
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ -> cleanup()
    end,
    ets:new(?TABLE, [set, named_table, {keypos, 1}]),
    ets:insert(?TABLE, {opts, Opts}), % special entry
    ok.

-spec cleanup() -> ok.
cleanup() ->
    ets:delete(?TABLE),
    ok.

-type file_kind() :: intern | {extern, [file:filename()]}.

-spec parse(file_kind(), file:filename()) -> [ast:form()].
parse(Kind, Path) ->
    PathNorm = filename:nativename(Path),
    Hash =
        case utils:hash_file(PathNorm) of
            {error, Reason} ->
                ?ABORT("Reading file ~p failed: ~200p", PathNorm, Reason);
            H -> H
        end,
    case ets:lookup(?TABLE, PathNorm) of
        [{_, {StoredHash, StoredKind, Forms}}] when Hash =:= StoredHash ->
            if Kind =:= StoredKind -> ok;
                true ->
                    ?ABORT("Previously parsed ~p with kind ~p, now requested for kind ~p",
                        PathNorm, StoredKind, Kind)
            end,
            ?LOG_TRACE("Retrieving parse result for ~p from cache", PathNorm),
            Forms;
        [] ->
            [{_, Opts}] = ets:lookup(?TABLE, opts),
            Forms = really_parse_file(Kind, PathNorm, Opts),
            ets:insert(?TABLE, {PathNorm, {Hash, Kind, Forms}}),
            Forms;
        X -> ?ABORT("Unexpected entry in parse cache for key ~p: ~p", PathNorm, X)
    end.

-spec really_parse_file(file_kind(), file:filename(), #opts{}) -> [ast:form()].
really_parse_file(Kind, File, Opts) ->
    ParseOpts =
        case Kind of
            intern -> #parse_opts{
                        includes = Opts#opts.includes,
                        defines = Opts#opts.defines
                    };
            {extern, Includes} ->
                #parse_opts{ verbose = false, includes = Includes, defines = Opts#opts.defines }
        end,
    ?LOG_DEBUG("Parsing ~s ...", File),
    RawForms = parse:parse_file_or_die(File, ParseOpts),
    if  Opts#opts.dump_raw -> ?LOG_NOTE("Raw forms in ~s:~n~p", File, RawForms);
        true -> ok
    end,
    ?LOG_TRACE("Parse result (raw):~n~120p", RawForms),

    IsIntern = Kind =:= intern,

    % SW (2023-07-06): there are some features that are not covered by the ast_check module.
    % Hence, we do not sanity check external modules. Especially some modules from the
    % erlang stdlib would fail sanity checking.
    if IsIntern andalso Opts#opts.sanity ->
            ?LOG_INFO("Checking whether parse result for ~p conforms to AST in ast_erl.erl ...",
                File),
            {RawSpec, _} = ast_check:parse_spec("src/ast_erl.erl"),
            lists:foreach(
                fun({Idx,Form}) ->
                    case ast_check:check_against_type(RawSpec, ast_erl, form, Form) of
                        true ->
                            ?LOG_DEBUG(
                                "Parse result of form ~p from ~s conforms to AST in ast_erl.erl",
                                Idx, File);
                        false ->
                            ?ABORT("Parse result of form ~p from ~s violates AST in ast_erl.erl",
                                Idx, File)
                    end
                end,
                lists:enumerate(1, RawForms));
       true -> ok
    end,

    ?LOG_DEBUG("Transforming ~s ...", File),
    Forms = ast_transform:trans(File, RawForms,
        if IsIntern -> full; true -> flat end),
    if  Opts#opts.dump ->
            ?LOG_NOTE("Transformed forms in ~s:~n~p", File, ast_utils:remove_locs(Forms));
        true -> ok
    end,
    ?LOG_TRACE("Parse result (after transform):~n~120p", Forms),
    Forms.
