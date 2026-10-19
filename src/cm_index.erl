-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module.

-export([
    load_index/3,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    has_external_dep_changed/3,
    insert/4
]).

-export_type([index/0]).

-include("log.hrl").
-include("etylizer_main.hrl").

-type index() :: {
    % OTP version, hash of rebar.lock, stamp of the options and the checker
    {string(), string(), term()},
    % map .erl-file -> {Sources, InterfaceHash}, Sources are the file and the headers it
    % includes, with their hashes
    #{file:filename() => {[{file:filename(), string() | {error, any()}}], string()}}
    }.

% Format of index on disk:
%-type stored_index() :: {
%    etylizer_index,
%    integer(), % version
%    index()
%}.

-define(INDEX_VERSION, 3).

-spec empty_index(file:filename(), term()) -> index().
empty_index(RebarLockFile, Stamp) ->
    Deps = get_external_deps(RebarLockFile, Stamp),
    {Deps, maps:new()}.

% replace index that cannot be used
-spec load_index(file:filename(), term(), file:filename()) -> index().
load_index(RebarLockFile, Stamp, Path) ->
    BadIndex =
        fun(Msg) ->
            ?LOG_WARN(Msg),
            empty_index(RebarLockFile, Stamp)
        end,
    case filelib:is_file(Path) of
        true ->
            case file:consult(Path) of
                {ok, [{etylizer_index, ?INDEX_VERSION, Index}]} ->
                    ?LOG_TRACE("Loading index from ~p", Path),
                    Index;
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
            empty_index(RebarLockFile, Stamp)
    end.

-spec save_index(file:filename(), index()) -> ok.
save_index(Path, Index) ->
    filelib:ensure_dir(Path),
    case file:write_file(Path, io_lib:format("~p.~n", [{etylizer_index, ?INDEX_VERSION, Index}])) of
        ok ->
            ?LOG_DEBUG("Stored index at ~p", Path),
            ok;
        {error, Reason} ->
            ?ABORT("Error occurred while trying to save index. Reason: ~s", Reason)
    end.

% Whether the file or one of the headers it includes changed.
-spec has_file_changed(file:filename(), index()) -> boolean().
has_file_changed(Path, {_, Index}) ->
    case maps:find(Path, Index) of
        {ok, {Sources, _}} ->
            lists:any(fun({File, Hash}) -> utils:hash_file(File) =/= Hash end, Sources);
        error -> true
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, {_, Index}) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash}} ->
            Interface = cm_module_interface:extract_interface_declaration(Forms),
            ?LOG_DEBUG("Interface of ~p: ~200p", Path, Interface),
            NewHash = utils:hash_sha1(io_lib:write(Interface)),
            OldInterfaceHash =/= NewHash
    end.

-spec get_external_deps(file:filename(), term()) -> {string(), string(), term()}.
get_external_deps(RebarLockFile, Stamp) ->
    OtpVersion = erlang:system_info(otp_release),
    RebarHash =
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
        end,
    {OtpVersion, RebarHash, Stamp}.

-spec has_external_dep_changed(file:filename(), term(), index()) -> {boolean(), index()}.
has_external_dep_changed(RebarLockFile, Stamp, {{StoredOtpVersion, StoredRebarHash, StoredStamp}, Index}) ->
    New = {OtpVersion, RebarHash, _} = get_external_deps(RebarLockFile, Stamp),
    Changed =
        case {OtpVersion =:= StoredOtpVersion, RebarHash =:= StoredRebarHash, Stamp =:= StoredStamp} of
            {true, true, true} -> false;
            {false, _, _} ->
                ?LOG_INFO("OTP version changed from ~p to ~p", StoredOtpVersion, OtpVersion),
                true;
            {true, false, _} ->
                ?LOG_INFO("Rebar lock file ~p changed", RebarLockFile),
                true;
            {true, true, false} ->
                ?LOG_INFO("The options or the checker changed"),
                true
        end,
    case Changed of
        true -> {true, {New, #{}}};
        false -> {false, {New, Index}}
    end.

-spec insert(file:filename(), ast:forms(), [file:filename()], index()) -> index().
insert(Path, Forms, Headers, {DepVersions, Index}) ->
    Sources = [{File, utils:hash_file(File)} || File <- [Path | Headers]],
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    InterfaceHash = utils:hash_sha1(io_lib:write(Interface)),
    {DepVersions, maps:put(Path, {Sources, InterfaceHash}, Index)}.
