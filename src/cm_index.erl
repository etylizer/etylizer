-module(cm_index).

% @doc This module maintains an index of files together with their hashes to enable
% the detection of changes in the content or the exported interface of the
% corresponding module.

-export([
    load_index/2,
    save_index/2,
    has_file_changed/2,
    has_exported_interface_changed/3,
    insert/3,
    remove/2
]).

-export_type([index/0]).

-include_lib("log.hrl").
-include_lib("ety_main.hrl").

-type index() :: #{file:filename() => {string(), string()}}.

-spec load_index(file:filename(), opts_mode()) -> index().
load_index(Path, Mode) ->
    BadIndex =
        fun(Msg) ->
            ?LOG_WARN(Msg),
            case Mode of
                test_mode -> throw("bad index: " ++ Msg);
                prod_mode -> maps:new()
            end
        end,
    case filelib:is_file(Path) of
        true ->
            case file:consult(Path) of
                {ok, [Index]} ->
                    ?LOG_INFO("Loading index from ~p", Path),
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
            NewHash = utils:hash_sha1(Content),
            NewHash =/= OldFileHash
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), index()) -> boolean().
has_exported_interface_changed(Path, Forms, Index) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash}} ->
            Interface = cm_module_interface:extract_interface_declaration(Forms),
            NewHash = utils:hash_sha1(io_lib:write(Interface)),
            OldInterfaceHash =/= NewHash
    end.

-spec insert(file:filename(), ast:forms(), index()) -> index().
insert(Path, Forms, Index) ->
    {ok, FileContent} = file:read_file(Path),
    FileHash = utils:hash_sha1(FileContent),
    Interface = cm_module_interface:extract_interface_declaration(Forms),
    InterfaceHash = utils:hash_sha1(io_lib:write(Interface)),
    maps:put(Path, {FileHash, InterfaceHash}, Index).

-spec remove(file:filename(), index()) -> index().
remove(Path, Index) ->
    maps:remove(Path, Index).
