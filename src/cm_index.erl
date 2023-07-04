-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module.

-export([
    load_index/1,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    insert/3,
    remove/2
]).

-export_type([index/0]).

-include_lib("log.hrl").

-type index() :: #{file:filename() => {binary(), binary()}}.

-spec load_index(file:filename()) -> index().
load_index(Path) ->
    case filelib:is_file(Path) of
        true ->
            case file:consult(Path) of
                {ok, [Index]} ->
                    ?LOG_INFO("Loading index from ~p", Path),
                    Index;
                {ok, []} ->
                    ?LOG_WARN("Empty index at ~p", Path),
                    maps:new();
                {ok, _} ->
                    ?LOG_WARN("Index with unexpected content at ~p", Path),
                    maps:new();
                {error, Reason} ->
                    ?LOG_WARN("Error occurred while trying to load existing index. Reason: ~s",
                        Reason),
                    maps:new()
            end;
        false ->
            ?LOG_INFO("No index exists at ~p, using empty index", Path),
            maps:new()
    end.

-spec save_index(file:filename(), index()) -> ok.
save_index(Path, Index) ->
    filelib:ensure_dir(Path),
    case file:write_file(Path, io_lib:format("~p.~n", [Index])) of
        ok ->
            ?LOG_INFO("Stored index at ~p", Path),
            ok;
        {error, Reason} ->
            ?ABORT("Error occurred while trying to save index. Reason: ~s", Reason)
    end.

-spec has_file_changed(file:filename(), index()) -> boolean().
has_file_changed(Path, Index) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {OldFileHash, _}} ->
            {ok, Content} = file:read_file(Path),
            NewHash = crypto:hash(sha, Content),
            not crypto:hash_equals(OldFileHash, NewHash)
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, Index) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash}} ->
            Interface = cm_module_interface:extract_interface_declaration(Forms),
            NewHash = crypto:hash(sha, io_lib:write(Interface)),
            not crypto:hash_equals(OldInterfaceHash, NewHash)
    end.

-spec insert(file:filename(), ast:forms(), index()) -> index().
insert(Path, Forms, Index) ->
    {ok, FileContent} = file:read_file(Path),
    FileHash = crypto:hash(sha, FileContent),
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    InterfaceHash = crypto:hash(sha, io_lib:write(Interface)),
    maps:put(Path, {FileHash, InterfaceHash}, Index).

-spec remove(file:filename(), index()) -> index().
remove(Path, Index) ->
    maps:remove(Path, Index).
