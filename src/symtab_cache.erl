-module(symtab_cache).

% Persists symtab to <project root>/_etylizer/symtab_cache
%
% Cache is valid only if the following match:
%  * code of the modules that compute entries 
%  * the OTP release 
%  * the options an entry depends on (parse options, gradual mode, overlay)

-include("log.hrl").
-include("etylizer_main.hrl").

-export([load/1, save/1, cached/2]).

-define(TABLE, symtab_cache).
-define(CODE_MODULES, [ast, ast_erl, ast_lib, ast_transform, ast_utils, attr, errors, ety_records,
                       feature_flags, parse, parse_cache, stdtypes, symtab, symtab_cache, utils, varenv]).

-spec load(#opts{}) -> ok.
load(Opts) ->
    ets:whereis(?TABLE) =:= undefined orelse ets:delete(?TABLE),
    ets:new(?TABLE, [public, named_table]),
    File = paths:symtab_cache_file_name(Opts),
    Stamp = stamp(Opts),
    case file:read_file(File) of
        {ok, Bin} ->
            case catch binary_to_term(Bin) of
                {Stamp, Entries} ->
                    ets:insert(?TABLE, Entries),
                    ?LOG_DEBUG("Loaded ~p cached entries from ~s", length(Entries), File);
                _ ->
                    ?LOG_DEBUG("Ignoring symtab cache ~s: unreadable or from another configuration", File)
            end;
        {error, Reason} ->
            ?LOG_DEBUG("No symtab cache at ~s: ~p", File, Reason)
    end,
    ok.

-spec save(#opts{}) -> ok.
save(Opts) ->
    File = paths:symtab_cache_file_name(Opts),
    Bin = term_to_binary({stamp(Opts), ets:tab2list(?TABLE)}),
    ets:delete(?TABLE),
    case filelib:ensure_dir(File) =:= ok andalso file:write_file(File, Bin) of
        ok -> ok;
        Err -> ?LOG_WARN("Could not write symtab cache ~s: ~p", File, Err)
    end.

% Compute returns the value and the files it was computed from.
-spec cached(term(), fun(() -> {T, [file:filename()]})) -> T.
cached(Key, Compute) ->
    case ets:whereis(?TABLE) of
        undefined -> element(1, Compute());
        _ ->
            case ets:lookup(?TABLE, Key) of
                [{_, Hashes, Value}] ->
                    case lists:all(fun({F, H}) -> utils:hash_file(F) =:= H end, Hashes) of
                        true -> Value;
                        false -> store(Key, Compute())
                    end;
                [] -> store(Key, Compute())
            end
    end.

-spec store(term(), {T, [file:filename()]}) -> T.
store(Key, {Value, Files}) ->
    ets:insert(?TABLE, {Key, [{F, utils:hash_file(F)} || F <- Files], Value}),
    Value.

-spec stamp(#opts{}) -> non_neg_integer().
stamp(Opts) ->
    Overlay = case Opts#opts.type_overlay of [] -> none; F -> utils:hash_file(F) end,
    erlang:phash2({[M:module_info(md5) || M <- ?CODE_MODULES],
                   erlang:system_info(otp_release), erlang:system_info(version),
                   Opts#opts.includes, Opts#opts.defines, Opts#opts.gradual_typing_mode, Overlay}).
