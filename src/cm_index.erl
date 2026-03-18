-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module, down to its functions.

-export([
    load_index/3,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    has_external_dep_changed/2,
    changed_functions/4,
    callers/2,
    insert/6
]).

-export_type([index/0]).

-include("log.hrl").
-include("etylizer_main.hrl").
-include("etylizer.hrl").
-include("cm_fun_deps.hrl").

% {Sources, InterfaceHash, ModuleInfo, Failed} as of the last check of a file.
% Sources are the file and the headers it includes, with their hashes.
% The functions in Failed did not type check.
-type file_entry() ::
    {[{file:filename(), string() | {error, any()}}], string(),
     cm_fun_deps:module_info(), [ast:fun_with_arity()]}.

-type index() :: {
    % OTP version and hash of rebar.lock
    {string(), string()},
    % map .erl-file -> file_entry()
    #{file:filename() => file_entry()}
    }.

% Format of index on disk:
%-type stored_index() :: {
%    etylizer_index,
%    integer(), % version
%    index()
%}.

-define(INDEX_VERSION, 6).

-spec empty_index(file:filename()) -> index().
empty_index(RebarLockFile) ->
    Deps = get_external_deps(RebarLockFile),
    {Deps, maps:new()}.

-spec load_index(file:filename(), file:filename(), opts_mode()) -> index().
load_index(RebarLockFile, Path, Mode) ->
    BadIndex =
        fun(Msg) ->
            ?LOG_WARN(Msg),
            case Mode of
                test_mode ->
                    ?LOG_WARN("Deleting stale index at ~p", Path),
                    file:delete(Path),
                    empty_index(RebarLockFile);
                prod_mode -> empty_index(RebarLockFile)
            end
        end,
    case filelib:is_file(Path) of
        true ->
            case file:consult(Path) of
                {ok, [{etylizer_index, ?INDEX_VERSION, Index}]} ->
                    ?LOG_TRACE("Loading index from ~p", Path),
                    ?assert_type(Index, index());
                {ok, []} ->
                    BadIndex(utils:sformat("Empty index at ~p", Path));
                {ok, _} ->
                    BadIndex(utils:sformat("Index with unexpected content at ~p", Path));
                {error, Reason} ->
                    BadIndex(utils:sformat(
                        "Error occurred while trying to load existing index. Reason: ~200p",
                        Reason))
            end;
        false ->
            ?LOG_DEBUG("No index exists at ~p, using empty index", Path),
            empty_index(RebarLockFile)
    end.

-spec save_index(file:filename(), index()) -> ok.
save_index(Path, Index) ->
    filelib:ensure_dir(Path),
    Formatted = lists:flatten(io_lib:format("~p.~n", [{etylizer_index, ?INDEX_VERSION, Index}])),
    case file:write_file(Path, ?assert_type(Formatted, string())) of
        ok -> ok;
        Error -> ?ABORT("Could not save the index at ~p: ~p", Path, Error)
    end.

% Whether the file or one of the headers it includes changed. A file with failed
% functions counts as changed, so that they are checked again.
-spec has_file_changed(file:filename(), index()) -> boolean().
has_file_changed(Path, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {Sources, _, _, []}} ->
            lists:any(fun({File, Hash}) -> utils:hash_file(File) =/= Hash end, Sources);
        _ -> true
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {_, InterfaceHash, _, _}} -> interface_hash(Forms) =/= InterfaceHash;
        error -> true
    end.

-spec interface_hash(ast:forms()) -> string().
interface_hash(Forms) ->
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    utils:hash_sha1(?assert_type(io_lib:write(Interface), iodata())).

-spec analyze(file:filename(), ast:forms()) -> cm_fun_deps:module_info().
analyze(Path, Forms) ->
    cm_fun_deps:analyze_module(ast_utils:modname_from_path(Path), Forms).

% The functions of a file to recheck: all of them if the file is new or its
% declarations changed. Otherwise the functions that are new, changed or failed,
% and those among them with a new or changed spec.
% OnlyRecheckChanged=false (default): previously-failed functions are always
% retried, even when body and spec are unchanged. This is the right behavior
% for batch/CI runs — a transient or context-dependent failure should not be
% baked into the index.
% OnlyRecheckChanged=true: only retry failed functions when body or spec
% changed. Used by watch-mode drivers (ety-watch) where re-running an
% unchanged failed function on every save is noise.
-spec changed_functions(file:filename(), ast:forms(), index(), boolean()) ->
    all | {[ast:fun_with_arity()], [ast:fun_with_arity()]}.
changed_functions(Path, Forms, {_, Index}, OnlyRecheckChanged) ->
    #module_info{decls_hash = DeclsHash, funs = Funs} = analyze(Path, Forms),
    case maps:find(Path, Index) of
        {ok, {_, _, #module_info{decls_hash = OldDeclsHash, funs = OldFuns}, Failed}}
                when OldDeclsHash =:= DeclsHash ->
            New = maps:to_list(Funs),
            Retry = case OnlyRecheckChanged of
                true -> [];
                false -> Failed
            end,
            Changed = [F || {F, Info} <- New,
                            lists:member(F, Retry) orelse maps:find(F, OldFuns) =/= {ok, Info}],
            SpecChanged = [F || {F, #fun_info{spec_hash = SpecHash}} <- New,
                                old_spec_hash(F, OldFuns) =/= SpecHash],
            {Changed, SpecChanged};
        _ ->
            all
    end.

-spec old_spec_hash(ast:fun_with_arity(), #{ast:fun_with_arity() => cm_fun_deps:fun_info()}) ->
    string() | new.
old_spec_hash(Fun, OldFuns) ->
    case maps:find(Fun, OldFuns) of
        {ok, #fun_info{spec_hash = SpecHash}} -> SpecHash;
        error -> new
    end.

% The functions calling one of the given functions, by file
-spec callers([cm_fun_deps:fun_id()], index()) -> [{file:filename(), [ast:fun_with_arity()]}].
callers([], _) -> [];
callers(Callees, {_, Index}) ->
    lists:filtermap(
        fun({Path, {_, _, #module_info{funs = Funs}, _}}) ->
            Callers = [F || {F, #fun_info{calls = Calls}} <- maps:to_list(Funs),
                            lists:any(fun(C) -> lists:member(C, Callees) end, Calls)],
            Callers =/= [] andalso {true, {Path, Callers}}
        end, maps:to_list(Index)).

-spec get_rebar_hash(file:filename()) -> string() | [].
get_rebar_hash(RebarLockFile) ->
    case utils:hash_file(RebarLockFile) of
        {error, _} ->
            case filelib:is_file(paths:rebar_config_from_lock_file(RebarLockFile)) of
                true ->
                    ?ABORT("Could not read rebar's lock file at ~p. Please build your project " ++
                            "with rebar before using etylizer.", RebarLockFile);
                false ->
                    []
            end;
        H -> H
    end.

-spec get_external_deps(file:filename()) -> {string(), string()}.
get_external_deps(RebarLockFile) ->
    OtpVersion = erlang:system_info(otp_release),
    RebarHash = get_rebar_hash(RebarLockFile),
    {OtpVersion, RebarHash}.

-spec has_external_dep_changed(file:filename(), index()) -> {boolean(), index()}.
has_external_dep_changed(RebarLockFile, {{StoredOtpVersion, StoredRebarHash}, Index}) ->
    {OtpVersion, RebarHash} = get_external_deps(RebarLockFile),
    Changed =
        case {OtpVersion =:= StoredOtpVersion, RebarHash =:= StoredRebarHash} of
            {true, true} -> false;
            {false, _} ->
                ?LOG_INFO("OTP version changed from ~p to ~p", StoredOtpVersion, OtpVersion),
                true;
            {true, false} ->
                ?LOG_INFO("Rebar lock file ~p changed", RebarLockFile),
                true
        end,
    NewIndex = {{OtpVersion, RebarHash}, Index},
    {Changed, NewIndex}.

% Records the state of a file, which includes the given headers, after checking the
% given functions, of which Failed did not type check. A function that failed before
% and was not checked now still counts as failed.
-spec insert(file:filename(), ast:forms(), [file:filename()], all | [ast:fun_with_arity()],
    [ast:fun_with_arity()], index()) -> index().
insert(Path, Forms, Headers, Checked, Failed, {DepVersions, Index}) ->
    ModInfo = analyze(Path, Forms),
    StillFailed =
        case {Checked, maps:find(Path, Index)} of
            {all, _} -> [];
            {_, {ok, {_, _, _, OldFailed}}} ->
                [F || F <- OldFailed -- Checked, maps:is_key(F, ModInfo#module_info.funs)];
            {_, error} -> []
        end,
    Sources = [{File, utils:hash_file(File)} || File <- [Path | Headers]],
    Entry = {Sources, interface_hash(Forms), ModInfo, Failed ++ StillFailed},
    {DepVersions, maps:put(Path, Entry, Index)}.
