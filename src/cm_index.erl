-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module.

-export([
    load_index/3,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    has_external_dep_changed/2,
    insert/3
]).

-export_type([index/0]).

-include("log.hrl").
-include("etylizer_main.hrl").
-include("etylizer.hrl").

-type index() :: {
    % OTP version and hash of rebar.lock
    {string(), string()},
    % map .erl-file -> {FileHash, InterfaceHash}
    #{file:filename() => {string(), string()}}
    }.

% Format of index on disk:
%-type stored_index() :: {
%    etylizer_index,
%    integer(), % version
%    index()
%}.

-define(INDEX_VERSION, 1).

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
                test_mode -> throw("bad index: " ++ Msg);
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
        {ok, {OldFileHash, _}} ->
            {ok, Content} = ?assert_type(file:read_file(Path), {ok, binary()}),
            NewHash = utils:hash_sha1(Content),
            NewHash =/= OldFileHash
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, {_, Index}) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash}} ->
            Interface = cm_module_interface:extract_interface_declaration(Forms),
            ?LOG_DEBUG("Interface of ~p: ~200p", Path, Interface),
            Written = ?assert_type(io_lib:write(Interface), iodata()),
            NewHash = utils:hash_sha1(Written),
            OldInterfaceHash =/= NewHash
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
    OtpVersion = ?assert_type(erlang:system_info(otp_release), string()),
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

-spec insert(file:filename(), ast:forms(), index()) -> index().
insert(Path, Forms, {DepVersions, Index}) ->
    {ok, FileContent} = ?assert_type(file:read_file(Path), {ok, binary()}),
    FileHash = utils:hash_sha1(FileContent),
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    Written = ?assert_type(io_lib:write(Interface), iodata()),
    InterfaceHash = utils:hash_sha1(Written),
    {DepVersions, maps:put(Path, {FileHash, InterfaceHash}, Index)}.
