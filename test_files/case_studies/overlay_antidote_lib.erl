%% Library specs for the antidote case study that overlay_riak_core_lite_lib.erl does not have. Each
%% spec is true for every call of the function; none says more than the function does. A result that
%% OTP gives as a type variable bound only in `when` (which fits every type) is term() here.
-module(overlay_antidote_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% ---------------------------------------------------------------------------------------------------
%% erlang

%% OTP: term(). The ?LOG_ macros of logger.hrl end in erlang:apply(logger, macro_log, [Location, Level |
%% Args]); logger:macro_log/3,4,5 give ok.
-spec 'erlang:apply'(logger, macro_log, [term()]) -> ok; (module(), atom(), [term()]) -> term().
'erlang:apply'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% maps: OTP says #{Key => Value, _ => _} for the map, with a result that is bound only there. With it
%% maps:put(K, maps:get(K, Map, 0) + N, Map) does not type check for a Map :: #{term() => integer()}.

%% the associations of the map and the new one
-spec 'maps:put'(K, V, #{K2 => V2}) -> #{K | K2 => V | V2}.
'maps:put'(_, _, _) -> error(overlay).

%% the value of the key, or the default
-spec 'maps:get'(term(), #{term() => V}, D) -> V | D.
'maps:get'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% rpc

%% OTP: Res | {badrpc, Reason} when Res :: term(), Reason :: term()
-spec 'rpc:call'(node(), module(), atom(), [term()]) -> term().
'rpc:call'(_, _, _, _) -> error(overlay).

-spec 'rpc:call'(node(), module(), atom(), [term()], 0..4294967295 | infinity) -> term().
'rpc:call'(_, _, _, _, _) -> error(overlay).

%% OTP: {ResL, BadNodes} when ResL :: [Res :: term() | {badrpc, Reason :: term()}], BadNodes :: [node()]
-spec 'rpc:multicall'([node()], module(), atom(), [term()]) -> {[term()], [node()]};
                     (module(), atom(), [term()], 0..4294967295 | infinity) -> {[term()], [node()]}.
'rpc:multicall'(_, _, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% ets and dets

%% OTP: Key | '$end_of_table' when Key :: term()
-spec 'ets:first'(ets:table()) -> term().
'ets:first'(_) -> error(overlay).

%% dets: OTP has {error, Reason} when Reason :: term() in the results; the name of a table is a term()
-spec 'dets:open_file'(Name, [{access, dets:access()} | {auto_save, dets:auto_save()} |
                              {estimated_no_objects, non_neg_integer()} | {file, file:name()} |
                              {max_no_slots, dets:no_slots()} | {min_no_slots, dets:no_slots()} |
                              {keypos, dets:keypos()} | {ram_file, boolean()} | {repair, boolean() | force} |
                              {type, dets:type()}]) ->
          {ok, Name} | {error, term()}.
'dets:open_file'(_, _) -> error(overlay).

-spec 'dets:sync'(term()) -> ok | {error, term()}.
'dets:sync'(_) -> error(overlay).

-spec 'dets:insert'(term(), tuple() | [tuple()]) -> ok | {error, term()}.
'dets:insert'(_, _) -> error(overlay).

-spec 'dets:delete_all_objects'(term()) -> ok | {error, term()}.
'dets:delete_all_objects'(_) -> error(overlay).

-spec 'dets:to_ets'(term(), EtsTab) -> EtsTab | {error, term()} when EtsTab :: ets:table().
'dets:to_ets'(_, _) -> error(overlay).
