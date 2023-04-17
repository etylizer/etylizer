-module(index).
-export([
    load_index/0,
    save_index/1,
    has_file_changed/2,
    has_exported_interface_changed/3,
    put_into_index/3
]).

-include_lib("log.hrl").

-spec load_index() -> map().
load_index() ->
    filelib:ensure_dir(".etylizer"),
    case filelib:is_file("./.etylizer/index") of
        true ->
            case file:read_file("./.etylizer/index") of
                {ok, FileContent} ->
                    decode_index(FileContent);
                {error, Reason} ->
                    ?ABORT("Error occurred while trying to load existing index. Reason: ~s", Reason)
            end;
        false -> maps:new()
    end.

-spec save_index(map()) -> ok.
save_index(Index) ->
    filelib:ensure_dir(".etylizer/"),
    case file:write_file(".etylizer/index", encode_index(Index)) of
        ok ->
            ok;
        {error, Reason} ->
            ?ABORT("Error occurred while trying to save index. Reason: ~s", Reason)
    end.

-spec encode_index(map()) -> binary().
encode_index(Index) ->
    NewIndex = maps:fold(
      fun(Key, Value, AccMap) ->
              maps:put(list_to_binary(Key), tuple_to_list(Value), AccMap)
      end, maps:new(), Index),
    jsone:encode(NewIndex).

-spec decode_index(binary()) -> map().
decode_index(FileContent) ->
    DecodedIndex = jsone:decode(FileContent),
    maps:fold(
     fun(Key, Value, AccMap) ->
             maps:put(binary_to_list(Key), list_to_tuple(Value), AccMap)
     end, maps:new(), DecodedIndex).

-spec has_file_changed(file:filename(), map()) -> boolean().
has_file_changed(Path, Index) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {OldFileHash, _}} ->
            {ok, Content} = file:read_file(Path),
            NewHash = crypto:hash(sha, Content),
            not crypto:hash_equals(OldFileHash, NewHash)
    end.

-spec has_exported_interface_changed(file:filename(), ast:forms(), map()) -> boolean().
has_exported_interface_changed(Path, Forms, Index) ->
    case maps:find(Path, Index) of
        error ->
            true;
        {ok, {_, OldInterfaceHash}} ->
            Interface = ast_utils:extract_interface_declaration(Forms),
            NewHash = crypto:hash(sha, io_lib:write(Interface)),
            not crypto:hash_equals(OldInterfaceHash, NewHash)
    end.

-spec put_into_index(file:filename(), ast:forms(), map()) -> map().
put_into_index(Path, Forms, Index) ->
    {ok, FileContent} = file:read_file(Path),
    FileHash = crypto:hash(sha, FileContent),
    Interface = ast_utils:extract_interface_declaration(Forms),
    InterfaceHash = crypto:hash(sha, io_lib:write(Interface)),
    maps:put(Path, {FileHash, InterfaceHash}, Index).
