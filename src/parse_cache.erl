-module(parse_cache).

-include("log.hrl").
-include("parse.hrl").
-include("etylizer_main.hrl").

-export([init/1, cleanup/0, parse/2, with_cache/2]).
-export_type([file_kind/0]).

-include("etylizer.hrl").

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

-spec with_cache(#opts{}, fun(() -> T)) -> T.
with_cache(Opts, Fun) ->
  parse_cache:init(Opts),
  try Fun()
  after
    parse_cache:cleanup()
  end.

-spec parse(file_kind(), file:filename()) -> [ast:form()].
parse(Kind, Path) ->
    PathNorm = utils:normalize_path(Path),
    Hash = hash_file(PathNorm),
    case ets:lookup(?TABLE, PathNorm) of
        [{_, {StoredHash, StoredKind, Forms}}] when Hash =:= StoredHash ->
            check_kind(Kind, ?assert_type(StoredKind, file_kind()), PathNorm),
            ?LOG_TRACE("Retrieving parse result for ~p from cache", PathNorm),
            ?assert_type(Forms, [ast:form()]);
        [] ->
            parse_and_cache(Kind, PathNorm, Hash);
        X -> ?ABORT("Unexpected entry in parse cache for key ~p: ~p", PathNorm, X)
    end.

-spec hash_file(file:filename()) -> string().
hash_file(PathNorm) ->
    case utils:hash_file(PathNorm) of
        {error, Reason} ->
            ?ABORT("Reading file ~p failed: ~200p", PathNorm, Reason);
        H -> H
    end.

-spec check_kind(file_kind(), file_kind(), file:filename()) -> ok.
check_kind(Kind, StoredKind, PathNorm) ->
    case Kind =:= StoredKind of
        true -> ok;
        false ->
            ?ABORT("Previously parsed ~p with kind ~p, now requested for kind ~p",
                PathNorm, StoredKind, Kind)
    end.

-spec parse_and_cache(file_kind(), file:filename(), string()) -> [ast:form()].
parse_and_cache(Kind, PathNorm, Hash) ->
    [{_, Opts}] = ?assert_pattern([{_, _}], ets:lookup(?TABLE, opts)),
    Forms = really_parse_file(Kind, PathNorm, ?assert_type(Opts, #opts{})),
    ets:insert(?TABLE, {PathNorm, {Hash, Kind, Forms}}),
    Forms.

-spec really_parse_file(file_kind(), file:filename(), #opts{}) -> [ast:form()].
really_parse_file(Kind, File, Opts) ->
    ParseOpts = make_parse_opts(Kind, Opts),
    ?LOG_DEBUG("Parsing ~s ...", File),
    RawForms = parse:parse_file_or_die(File, ParseOpts),
    ?LOG_DEBUG("Finished parsing ~s", File),
    case Opts#opts.dump_raw of
        true -> ?LOG_NOTE("Raw forms in ~s:~n~p", File, RawForms);
        false -> ok
    end,
    ?LOG_TRACE("Parse result (raw):~n~120p", RawForms),
    maybe_sanity_check(Kind, File, Opts, RawForms),
    transform_forms(Kind, File, Opts, RawForms).

-spec make_parse_opts(file_kind(), #opts{}) -> #parse_opts{}.
make_parse_opts(Kind, Opts) ->
    case Kind of
        intern -> #parse_opts{
                    verbose = Opts#opts.verbose,
                    includes = Opts#opts.includes,
                    defines = Opts#opts.defines
                };
        {extern, Includes} ->
            #parse_opts{ verbose = false, includes = Includes, defines = Opts#opts.defines }
    end.

% SW (2023-07-06): there are some features that are not covered by the ast_check module.
% Hence, we do not sanity check external modules. Especially some modules from the
% erlang stdlib would fail sanity checking.
-spec maybe_sanity_check(file_kind(), file:filename(), #opts{}, [ast_erl:form()]) -> ok.
maybe_sanity_check(intern, File, Opts, RawForms) ->
    case Opts#opts.sanity of
        true ->
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
                lists:enumerate(1, RawForms)),
            ok;
        false -> ok
    end;
maybe_sanity_check({extern, _}, _File, _Opts, _RawForms) ->
    ok.

-spec transform_forms(file_kind(), file:filename(), #opts{}, [ast_erl:form()]) -> [ast:form()].
transform_forms(Kind, File, Opts, RawForms) ->
    ?LOG_DEBUG("Transforming ~s ...", File),
    TransMode = case Kind of intern -> full; {extern, _} -> flat end,
    Forms = ast_transform:trans(File, RawForms, TransMode),
    case Opts#opts.dump of
        true -> ?LOG_NOTE("Transformed forms in ~s:~n~p", File, ast_utils:remove_locs(Forms));
        false -> ok
    end,
    ?LOG_TRACE("Parse result (after transform):~n~120p", Forms),
    Forms.
