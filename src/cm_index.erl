-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module. Supports function-level granularity for incremental type checking.

-export([
    load_index/3,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    has_external_dep_changed/2,
    insert/3,
    insert/4,
    insert_fun_index/5,
    changed_functions/3,
    prune/2
]).

-export_type([index/0, file_index_entry/0]).

-include("log.hrl").
-include("etylizer_main.hrl").
-include("etylizer.hrl").

% Per-function hashes: {atom(), arity()} => {BodyHash, SpecHash} | {failed, SpecHash}
-type fun_index_entry() :: #{{atom(), arity()} => {string(), string()} | {failed, string()}}.

% File index entry: {FileHash, InterfaceHash, DeclsHash, FunIndex}
-type file_index_entry() :: {string(), string(), string(), fun_index_entry()}.

-type index() :: {
    % OTP version and hash of rebar.lock
    {string(), string()},
    % map .erl-file -> file_index_entry()
    #{file:filename() => file_index_entry()}
    }.

% Format of index on disk:
%-type stored_index() :: {
%    etylizer_index,
%    integer(), % version
%    index()
%}.

-define(INDEX_VERSION, 3).

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
    ?assert_pattern(ok, file:write_file(Path, ?assert_type(Formatted, string()))).

-spec has_file_changed(file:filename(), index()) -> boolean().
has_file_changed(Path, {_, Index}) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {OldFileHash, _, _, _}} ->
            {ok, Content} = ?assert_type(file:read_file(Path), {ok, binary()}),
            NewHash = utils:hash_sha1(Content),
            NewHash =/= OldFileHash
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, {_, Index}) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash, _, _}} ->
            Interface = cm_module_interface:extract_interface_declaration(Forms),
            ?LOG_DEBUG("Interface of ~p: ~200p", Path, Interface),
            Written = ?assert_type(io_lib:write(Interface), iodata()),
            NewHash = utils:hash_sha1(Written),
            OldInterfaceHash =/= NewHash
    end.

% @doc Compute which functions in a file need rechecking.
% Returns {all | [{atom(), arity()}], DeclsChanged :: boolean()}.
-spec changed_functions(file:filename(), cm_fun_deps:module_info(), index()) ->
    {all | [ast:fun_with_arity()], boolean()}.
changed_functions(Path, ModInfo, {_, Index}) ->
    NewDeclsHash = ?assert_type(maps:get(decls_hash, ModInfo), string()),
    NewFuns = ?assert_type(maps:get(funs, ModInfo), #{cm_fun_deps:fun_id() => cm_fun_deps:fun_info()}),
    case maps:find(Path, Index) of
        error ->
            % File not in index, everything is new
            {all, true};
        {ok, {_, _, OldDeclsHash, OldFunIndex}} ->
            case NewDeclsHash =/= OldDeclsHash of
                true ->
                    % Types/records/exports changed, must recheck all
                    ?LOG_DEBUG("Declarations changed in ~p, rechecking all functions", Path),
                    {all, true};
                false ->
                    % Check each function individually
                    ChangedFuns = maps:fold(
                        fun({_Mod, Name, Arity}, FunInfo, Acc) ->
                            NewBodyHash = ?assert_type(maps:get(body_hash, FunInfo), string()),
                            NewSpecHash = ?assert_type(maps:get(spec_hash, FunInfo), string()),
                            case maps:find({Name, Arity}, OldFunIndex) of
                                error ->
                                    % New function
                                    [{Name, Arity} | Acc];
                                {ok, {failed, _}} ->
                                    % Previously failed, needs retry
                                    [{Name, Arity} | Acc];
                                {ok, {OldBodyHash, OldSpecHash}} ->
                                    BodyChanged = NewBodyHash =/= OldBodyHash,
                                    SpecChanged = NewSpecHash =/= OldSpecHash,
                                    case {BodyChanged, SpecChanged} of
                                        {false, false} -> Acc;
                                        _ -> [{Name, Arity} | Acc]
                                    end
                            end
                        end, [], NewFuns),
                    {ChangedFuns, false}
            end
    end.

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

% @doc Backward-compatible insert without failed functions tracking.
-spec insert(file:filename(), ast:forms(), index()) -> index().
insert(Path, Forms, Index) ->
    insert(Path, Forms, [], Index).

% @doc Insert file index entry, excluding functions that failed type checking.
% Failed functions are omitted from the fun index so they are re-checked on the next run.
% If any functions failed, a dummy file hash is used to force re-processing of the file.
-spec insert(file:filename(), ast:forms(), [{atom(), arity()}], index()) -> index().
insert(Path, Forms, FailedFuns, Index) ->
    ModName = ast_utils:modname_from_path(Path),
    ModInfo = cm_fun_deps:analyze_module(ModName, Forms),
    insert_fun_index(Path, Forms, ModInfo, FailedFuns, Index).

% @doc Insert file index entry using pre-computed module info and forms.
-spec insert_fun_index(file:filename(), ast:forms(), cm_fun_deps:module_info(),
    [{atom(), arity()}], index()) -> index().
insert_fun_index(Path, Forms, ModInfo, FailedFuns, {DepVersions, Index}) ->
    {ok, FileContent} = ?assert_type(file:read_file(Path), {ok, binary()}),
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    Written = ?assert_type(io_lib:write(Interface), iodata()),
    InterfaceHash = utils:hash_sha1(Written),
    DeclsHash = ?assert_type(maps:get(decls_hash, ModInfo), string()),
    Funs = ?assert_type(maps:get(funs, ModInfo), #{cm_fun_deps:fun_id() => cm_fun_deps:fun_info()}),
    FailedSet = sets:from_list(FailedFuns, [{version, 2}]),
    FunIndex = maps:fold(
        fun({_Mod, Name, Arity}, FunInfo, Acc) ->
            case sets:is_element({Name, Arity}, FailedSet) of
                true ->
                    SpecHash = ?assert_type(maps:get(spec_hash, FunInfo), string()),
                    maps:put({Name, Arity}, {failed, SpecHash}, Acc);
                false ->
                    BodyHash = ?assert_type(maps:get(body_hash, FunInfo), string()),
                    SpecHash = ?assert_type(maps:get(spec_hash, FunInfo), string()),
                    maps:put({Name, Arity}, {BodyHash, SpecHash}, Acc)
            end
        end, maps:new(), Funs),
    % Use a dummy file hash when there are failures, so the file is re-processed next run
    FileHash = case FailedFuns of
        [] -> utils:hash_sha1(FileContent);
        _ -> ""
    end,
    {DepVersions, maps:put(Path, {FileHash, InterfaceHash, DeclsHash, FunIndex}, Index)}.

% @doc Remove index entries for files not in the given source list.
-spec prune(index(), [file:filename()]) -> index().
prune({DepVersions, Index}, SourceList) ->
    SourceSet = sets:from_list(SourceList, [{version, 2}]),
    PrunedIndex = maps:filter(
        fun(Path, _) -> sets:is_element(Path, SourceSet) end,
        Index),
    {DepVersions, PrunedIndex}.
