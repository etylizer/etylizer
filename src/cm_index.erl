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

-include_lib("log.hrl").

-define(ETYLIZER_DIR, ".etylizer").

-type index() :: #{file:filename() => {binary(), binary()}}.

-spec load_index(file:filename()) -> index().
load_index(FileName) ->
    filelib:ensure_dir(?ETYLIZER_DIR),
    Path = filename:join(?ETYLIZER_DIR, FileName),
    case filelib:is_file(Path) of
        true ->
            case file:read_file(Path) of
                {ok, FileContent} ->
                    decode_index(FileContent);
                {error, Reason} ->
                    ?ABORT("Error occurred while trying to load existing index. Reason: ~s", Reason)
            end;
        false -> maps:new()
    end.

-spec save_index(file:filename(), index()) -> ok.
save_index(FileName, Index) ->
    filelib:ensure_dir(?ETYLIZER_DIR),
    case file:write_file(filename:join(?ETYLIZER_DIR, FileName), encode_index(Index)) of
        ok ->
            ok;
        {error, Reason} ->
            ?ABORT("Error occurred while trying to save index. Reason: ~s", Reason)
    end.

-spec encode_index(index()) -> binary().
encode_index(Index) ->
    NewIndex = maps:fold(
      fun(Key, {FileHash, InterfaceHash}, AccMap) ->
              maps:put(list_to_binary(Key), [base64:encode(FileHash), base64:encode(InterfaceHash)], AccMap)
      end, maps:new(), Index),
    jsone:encode(NewIndex).

-spec decode_index(binary()) -> index().
decode_index(FileContent) ->
    DecodedIndex = jsone:decode(FileContent),
    maps:fold(
     fun(Key, Value, AccMap) ->
             {FileHash, InterfaceHash} = list_to_tuple(Value),
             maps:put(binary_to_list(Key), {base64:decode(FileHash), base64:decode(InterfaceHash)}, AccMap)
     end, maps:new(), DecodedIndex).

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
            Interface = ast_utils:extract_interface_declaration(Forms),
            NewHash = crypto:hash(sha, io_lib:write(Interface)),
            not crypto:hash_equals(OldInterfaceHash, NewHash)
    end.

-spec insert(file:filename(), ast:forms(), index()) -> index().
insert(Path, Forms, Index) ->
    {ok, FileContent} = file:read_file(Path),
    FileHash = crypto:hash(sha, FileContent),
    Interface = ast_utils:extract_interface_declaration(Forms),
    InterfaceHash = crypto:hash(sha, io_lib:write(Interface)),
    maps:put(Path, {FileHash, InterfaceHash}, Index).

-spec remove(file:filename(), index()) -> index().
remove(Path, Index) ->
    maps:remove(Path, Index).
