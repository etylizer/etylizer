%% A spec for each of the 308 functions of apps/antidote that have none in the source (antidote case
%% study). The types are those of the three headers of antidote, included here, of the module of the
%% function, and of the behaviours (gen_server, gen_statem, gen_event, supervisor, riak_core_vnode).
%%
%% A type that is, or contains, a record cannot be named through the headers here: it is written
%% with the module of the function in front, as that module has it from its own include (cure:txid(),
%% clocksi_vnode:tx(), logging_vnode:log_record(), ...). A helper type that is a tuple stands for the
%% record of a module that has no type for it (the state of clocksi_vnode and of logging_vnode).
%% A spec names the types of another module only where every module that calls the function refers
%% to that module as well; the checker does not find them otherwise.
-module(overlay_antidote).
-compile([export_all, nowarn_export_all]).

-include("antidote.hrl").
-include("inter_dc_repl.hrl").
-include_lib("riak_core/include/riak_core_vnode.hrl").

%% the write set of a transaction for one partition, as clocksi_vnode:update_materializer/3 has it,
%% and the write sets of a transaction by partition (#state.updated_partitions of the coordinator)
-type write_set() :: [{key(), type(), effect()}].
-type updated_partitions() :: [{index_node(), write_set()}].

%% what gen_server:start_link/3,4 and supervisor:start_link/2,3 give, as the specs of the source say it
%% (meta_data_sender:start_link/1, stable_meta_data_server:start_link/0)
-type start_link_ret() :: {ok, pid()} | ignore | {error, term()}.

%% the result of init/1 of a supervisor
-type sup_init() :: {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.

%% handoff_dest() of riak_core_vnode.hrl with riak_core_handoff_manager:ho_type() spelled out: three
%% of the six vnode modules do not include that header and so do not refer to riak_core_handoff_manager
-type handoff_target() :: {ownership | hinted | repair | resize, {partition_id(), node()}}.

%% ---------------------------------------------------------------------------------------------
%% antidote
%% ---------------------------------------------------------------------------------------------

-spec 'antidote:get_log_operations_internal'([{bound_object(), snapshot_time()}],
                                             [[{non_neg_integer(), antidote:clocksi_payload()}]]) ->
          {ok, [[{non_neg_integer(), antidote:clocksi_payload()}]]} | {error, reason()}.
'antidote:get_log_operations_internal'(_, _) -> error(overlay).

-spec 'antidote:create_bucket'(bucket(), type()) -> {error, operation_not_supported}.
'antidote:create_bucket'(_, _) -> error(overlay).

-spec 'antidote:create_object'(key(), type(), bucket()) -> {error, operation_not_supported}.
'antidote:create_object'(_, _, _) -> error(overlay).

-spec 'antidote:delete_object'(bound_object()) -> {error, operation_not_supported}.
'antidote:delete_object'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_app
%% ---------------------------------------------------------------------------------------------

-spec 'antidote_app:start'(application:start_type(), term()) -> {ok, pid()} | {error, term()}.
'antidote_app:start'(_, _) -> error(overlay).

%% throws {error, invalid_data_dir} when the directory cannot be created
-spec 'antidote_app:validate_data_dir'() -> ok.
'antidote_app:validate_data_dir'() -> error(overlay).

-spec 'antidote_app:stop'(term()) -> ok.
'antidote_app:stop'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_console
%% ---------------------------------------------------------------------------------------------

%% the arguments of a console command are strings
-spec 'antidote_console:staged_join'([string()]) -> ok | error.
'antidote_console:staged_join'(_) -> error(overlay).

%% JoinFn is fun riak_core:staged_join/1
-spec 'antidote_console:join'(string(), fun((string()) -> ok | {error, term()}), string(), [term()]) -> ok | error.
'antidote_console:join'(_, _, _, _) -> error(overlay).

-spec 'antidote_console:down'([string()]) -> ok | error.
'antidote_console:down'(_) -> error(overlay).

-spec 'antidote_console:ringready'([]) -> ok | error.
'antidote_console:ringready'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_error_monitor, antidote_warning_monitor: handlers of logger
%% ---------------------------------------------------------------------------------------------

-spec 'antidote_error_monitor:log'(logger:log_event(), logger:handler_config()) -> ok.
'antidote_error_monitor:log'(_, _) -> error(overlay).

-spec 'antidote_warning_monitor:log'(logger:log_event(), logger:handler_config()) -> ok.
'antidote_warning_monitor:log'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_hooks
%% ---------------------------------------------------------------------------------------------

%% the argument and the result of a commit hook: update_object() of the comment at the top of the module
-type hook_object() :: {{key(), bucket()}, type(), op()}.

%% Prefix is ?PREFIX_PRE or ?PREFIX_POST
-spec 'antidote_hooks:register_hook'({commit_hooks, pre | post}, bucket(), module_name(), function_name()) ->
          ok | {error, function_not_exported}.
'antidote_hooks:register_hook'(_, _, _, _) -> error(overlay).

%% what register_hook/4 stores, undefined when there is no hook or after unregister_hook/2
-spec 'antidote_hooks:get_hooks'(pre_commit | post_commit, bucket()) -> {module_name(), function_name()} | undefined.
'antidote_hooks:get_hooks'(_, _) -> error(overlay).

-spec 'antidote_hooks:test_commit_hook'(hook_object()) -> {ok, hook_object()}.
'antidote_hooks:test_commit_hook'(_) -> error(overlay).

-spec 'antidote_hooks:test_increment_hook'(hook_object()) -> {ok, hook_object()}.
'antidote_hooks:test_increment_hook'(_) -> error(overlay).

-spec 'antidote_hooks:test_post_hook'(hook_object()) -> {ok, hook_object()}.
'antidote_hooks:test_post_hook'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_node_event_handler: a gen_event handler of riak_core_node_watcher_events
%% ---------------------------------------------------------------------------------------------

%% the one event of riak_core_node_watcher_events
-spec 'antidote_node_event_handler:handle_event'({service_update, [atom()]}, antidote_node_event_handler:state()) ->
          {ok, antidote_node_event_handler:state()}.
'antidote_node_event_handler:handle_event'(_, _) -> error(overlay).

-spec 'antidote_node_event_handler:handle_call'(term(), antidote_node_event_handler:state()) ->
          {ok, ok, antidote_node_event_handler:state()}.
'antidote_node_event_handler:handle_call'(_, _) -> error(overlay).

-spec 'antidote_node_event_handler:handle_info'(term(), antidote_node_event_handler:state()) ->
          {ok, antidote_node_event_handler:state()}.
'antidote_node_event_handler:handle_info'(_, _) -> error(overlay).

-spec 'antidote_node_event_handler:terminate'(term(), antidote_node_event_handler:state()) -> ok.
'antidote_node_event_handler:terminate'(_, _) -> error(overlay).

-spec 'antidote_node_event_handler:code_change'(term(), antidote_node_event_handler:state(), term()) ->
          {ok, antidote_node_event_handler:state()}.
'antidote_node_event_handler:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_pb_protocol: a ranch_protocol
%% ---------------------------------------------------------------------------------------------

%% the callback of ranch_protocol
-spec 'antidote_pb_protocol:start_link'(ranch:ref(), module(), any()) -> {ok, pid()}.
'antidote_pb_protocol:start_link'(_, _, _) -> error(overlay).

%% the process that start_link/3 spawns: it ends with loop/2
-spec 'antidote_pb_protocol:init'(ranch:ref(), module(), any()) -> ok.
'antidote_pb_protocol:init'(_, _, _) -> error(overlay).

%% the socket as handle/3 has it in the source: any
-spec 'antidote_pb_protocol:loop'(any(), module()) -> ok.
'antidote_pb_protocol:loop'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_pb_sup
%% ---------------------------------------------------------------------------------------------

-spec 'antidote_pb_sup:start_link'() -> start_link_ret().
'antidote_pb_sup:start_link'() -> error(overlay).

-spec 'antidote_pb_sup:init'([]) -> sup_init().
'antidote_pb_sup:init'(_) -> error(overlay).

-spec 'antidote_pb_sup:pb_listener'() -> supervisor:child_spec().
'antidote_pb_sup:pb_listener'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_ring_event_handler: a gen_event handler of riak_core_ring_events
%% ---------------------------------------------------------------------------------------------

%% the one event of riak_core_ring_events
-spec 'antidote_ring_event_handler:handle_event'({ring_update, riak_core_ring:riak_core_ring()},
                                                 antidote_ring_event_handler:state()) ->
          {ok, antidote_ring_event_handler:state()}.
'antidote_ring_event_handler:handle_event'(_, _) -> error(overlay).

-spec 'antidote_ring_event_handler:handle_call'(term(), antidote_ring_event_handler:state()) ->
          {ok, ok, antidote_ring_event_handler:state()}.
'antidote_ring_event_handler:handle_call'(_, _) -> error(overlay).

-spec 'antidote_ring_event_handler:handle_info'(term(), antidote_ring_event_handler:state()) ->
          {ok, antidote_ring_event_handler:state()}.
'antidote_ring_event_handler:handle_info'(_, _) -> error(overlay).

-spec 'antidote_ring_event_handler:terminate'(term(), antidote_ring_event_handler:state()) -> ok.
'antidote_ring_event_handler:terminate'(_, _) -> error(overlay).

-spec 'antidote_ring_event_handler:code_change'(term(), antidote_ring_event_handler:state(), term()) ->
          {ok, antidote_ring_event_handler:state()}.
'antidote_ring_event_handler:code_change'(_, _, _) -> error(overlay).

-spec 'antidote_ring_event_handler:update_status'() -> ok.
'antidote_ring_event_handler:update_status'() -> error(overlay).

-spec 'antidote_ring_event_handler:claim_percent'(riak_core_ring:riak_core_ring(), node()) -> float().
'antidote_ring_event_handler:claim_percent'(_, _) -> error(overlay).

%% Changes is the list of pending transfers of riak_core_status:ring_status/0, only tested for []
-spec 'antidote_ring_event_handler:future_claim_percentage'(list(), riak_core_ring:riak_core_ring(), node()) -> float().
'antidote_ring_event_handler:future_claim_percentage'(_, _, _) -> error(overlay).

%% 1: up, -1: down and marked down, -2: down, 2: marked down
-spec 'antidote_ring_event_handler:node_availability'(node(), [node()], [node()]) -> integer().
'antidote_ring_event_handler:node_availability'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_stats: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'antidote_stats:start_link'() -> start_link_ret().
'antidote_stats:start_link'() -> error(overlay).

-spec 'antidote_stats:handle_call'(term(), gen_server:from(), antidote_stats:state()) -> {reply, ok, antidote_stats:state()}.
'antidote_stats:handle_call'(_, _, _) -> error(overlay).

-spec 'antidote_stats:handle_cast'(term(), antidote_stats:state()) -> {noreply, antidote_stats:state()}.
'antidote_stats:handle_cast'(_, _) -> error(overlay).

%% the two timers of init/1, no clause for other messages
-spec 'antidote_stats:handle_info'(periodic_update | periodic_expensive_update, antidote_stats:state()) ->
          {noreply, antidote_stats:state()}.
'antidote_stats:handle_info'(_, _) -> error(overlay).

-spec 'antidote_stats:terminate'(term(), antidote_stats:state()) -> ok.
'antidote_stats:terminate'(_, _) -> error(overlay).

-spec 'antidote_stats:code_change'(term(), antidote_stats:state(), term()) -> {ok, antidote_stats:state()}.
'antidote_stats:code_change'(_, _, _) -> error(overlay).

-spec 'antidote_stats:update_staleness'() -> ok.
'antidote_stats:update_staleness'() -> error(overlay).

%% in milliseconds
-spec 'antidote_stats:calculate_staleness'() -> non_neg_integer().
'antidote_stats:calculate_staleness'() -> error(overlay).

-spec 'antidote_stats:to_microsec'(erlang:timestamp()) -> non_neg_integer().
'antidote_stats:to_microsec'(_) -> error(overlay).

-spec 'antidote_stats:update_dc_count'() -> ok.
'antidote_stats:update_dc_count'() -> error(overlay).

%% the monitored processes as the field monitored_processes of the state has them: list(). The
%% boolean says whether to go on collecting
-spec 'antidote_stats:update_processes_info'(list()) -> {boolean(), list()}.
'antidote_stats:update_processes_info'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% antidote_sup
%% ---------------------------------------------------------------------------------------------

-spec 'antidote_sup:start_link'() -> start_link_ret().
'antidote_sup:start_link'() -> error(overlay).

-spec 'antidote_sup:init'([]) -> sup_init().
'antidote_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% bcounter_mgr: a gen_server
%% ---------------------------------------------------------------------------------------------

%% antidote_crdt_counter_b:antidote_crdt_counter_b_op(), antidote_crdt_counter_b() and
%% antidote_crdt_counter_b_effect(), spelled out: clocksi_downstream calls generate_downstream/3 and
%% refers neither to antidote_crdt_counter_b nor to orddict. The id of a replica is a term() there,
%% antidote uses the dcid(); the two orddicts of the counter are written as the lists of pairs they are.
-type bcounter_op() :: {increment | decrement, {pos_integer(), term()}} | {transfer, {pos_integer(), term(), term()}}.
-type bcounter() :: {[{{term(), term()}, pos_integer()}], [{term(), pos_integer()}]}.
-type bcounter_effect() :: {{increment | decrement, pos_integer()} | {transfer, pos_integer(), term()}, term()}.
%% the request of a remote DC for permissions: {Key, Amount, Requester}
-type bcounter_transfer() :: {{key(), bucket()}, pos_integer(), dcid()}.

-spec 'bcounter_mgr:start_link'() -> start_link_ret().
'bcounter_mgr:start_link'() -> error(overlay).

-spec 'bcounter_mgr:generate_downstream'({key(), bucket()}, bcounter_op(), bcounter()) ->
          {ok, bcounter_effect()} | {error, no_permissions}.
'bcounter_mgr:generate_downstream'(_, _, _) -> error(overlay).

-spec 'bcounter_mgr:process_transfer'({transfer, bcounter_transfer()}) -> ok.
'bcounter_mgr:process_transfer'(_) -> error(overlay).

%% no clause for other messages
-spec 'bcounter_mgr:handle_cast'({transfer, bcounter_transfer()}, bcounter_mgr:state()) -> {noreply, bcounter_mgr:state()}.
'bcounter_mgr:handle_cast'(_, _) -> error(overlay).

%% the one request, of generate_downstream/3 for a decrement
-spec 'bcounter_mgr:handle_call'({consume, {key(), bucket()}, {decrement, {pos_integer(), dcid()}}, bcounter()},
                                 gen_server:from(), bcounter_mgr:state()) ->
          {reply, {ok, bcounter_effect()} | {error, no_permissions}, bcounter_mgr:state()}.
'bcounter_mgr:handle_call'(_, _, _) -> error(overlay).

%% the timer of init/1 and of this function, no clause for other messages
-spec 'bcounter_mgr:handle_info'(transfer_periodic, bcounter_mgr:state()) -> {noreply, bcounter_mgr:state()}.
'bcounter_mgr:handle_info'(_, _) -> error(overlay).

-spec 'bcounter_mgr:terminate'(term(), bcounter_mgr:state()) -> ok.
'bcounter_mgr:terminate'(_, _) -> error(overlay).

-spec 'bcounter_mgr:code_change'(term(), bcounter_mgr:state(), term()) -> {ok, bcounter_mgr:state()}.
'bcounter_mgr:code_change'(_, _, _) -> error(overlay).

%% the queue of the state, #state.req_queue :: orddict:orddict(): per key the requests {Amount, Time}
-spec 'bcounter_mgr:queue_request'({key(), bucket()}, integer(), orddict:orddict()) -> orddict:orddict().
'bcounter_mgr:queue_request'(_, _, _) -> error(overlay).

%% what is still missing after asking the other DCs
-spec 'bcounter_mgr:request_remote'(integer(), {key(), bucket()}) -> integer().
'bcounter_mgr:request_remote'(_, _) -> error(overlay).

-spec 'bcounter_mgr:do_request'(dcid(), dcid(), {key(), bucket()}, integer()) -> ok | unknown_dc.
'bcounter_mgr:do_request'(_, _, _, _) -> error(overlay).

%% the other DCs with the permissions they hold, fewest first
-spec 'bcounter_mgr:pref_list'(bcounter()) -> [{dcid(), non_neg_integer()}].
'bcounter_mgr:pref_list'(_) -> error(overlay).

%% the callback of inter_dc_query_dealer:perform_request/4
-spec 'bcounter_mgr:request_response'(binary()) -> ok.
'bcounter_mgr:request_response'(_) -> error(overlay).

%% #state.last_transfers :: orddict:orddict(); the period in microseconds
-spec 'bcounter_mgr:cancel_consecutive_req'(orddict:orddict(), non_neg_integer()) -> orddict:orddict().
'bcounter_mgr:cancel_consecutive_req'(_, _) -> error(overlay).

-spec 'bcounter_mgr:clear_pending_req'(orddict:orddict(), non_neg_integer()) -> orddict:orddict().
'bcounter_mgr:clear_pending_req'(_, _) -> error(overlay).

-spec 'bcounter_mgr:can_process'({key(), bucket()}, dcid(), orddict:orddict()) -> boolean().
'bcounter_mgr:can_process'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% clocksi_interactive_coord: a gen_statem with state functions
%% ---------------------------------------------------------------------------------------------

%% The specs of the source (execute_op/3, single_committing/3, execute_command/4, prepare/1,
%% prepare_done/2) say gen_statem:event_handler_result(state()), which makes the record the type of the
%% state name. The specs here say what the callback StateName/3 of gen_statem says: the name of a state
%% is an atom, the record is the data.
-type coord_result() :: gen_statem:event_handler_result(atom(), clocksi_interactive_coord:state()).

-spec 'clocksi_interactive_coord:stop'(pid()) -> ok.
'clocksi_interactive_coord:stop'(_) -> error(overlay).

%% no caller in antidote
-spec 'clocksi_interactive_coord:finish_op'(pid(), key(), term()) -> ok.
'clocksi_interactive_coord:finish_op'(_, _, _) -> error(overlay).

%% the data is the atom ignore until the transaction starts
-spec 'clocksi_interactive_coord:init'([]) -> {ok, wait_for_start_transaction, ignore}.
'clocksi_interactive_coord:init'(_) -> error(overlay).

%% the request of cure:clocksi_istart_tx/2
-spec 'clocksi_interactive_coord:wait_for_start_transaction'({call, gen_statem:from()},
                                                             {start_tx, snapshot_time() | ignore, txn_properties()},
                                                             ignore) ->
          coord_result().
'clocksi_interactive_coord:wait_for_start_transaction'(_, _, _) -> error(overlay).

%% The replies of the vnodes come as messages {'$gen_event', Reply}: the clause for info hands the
%% reply to the clause for cast. The events are those of the clauses, as in the spec of single_committing/3.
-spec 'clocksi_interactive_coord:receive_prepared'
        (cast, {prepared, clock_time()} | abort | timeout, clocksi_interactive_coord:state()) -> coord_result();
        (info, {any(), any()}, clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:receive_prepared'(_, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:committing'({call, gen_statem:from()}, commit, clocksi_interactive_coord:state()) ->
          coord_result().
'clocksi_interactive_coord:committing'(_, _, _) -> error(overlay).

%% every cast other than ack_abort is dropped
-spec 'clocksi_interactive_coord:receive_aborted'
        (cast, term(), clocksi_interactive_coord:state()) -> coord_result();
        (info, {any(), any()}, clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:receive_aborted'(_, _, _) -> error(overlay).

%% the cast of clocksi_readitem:async_read_data_item/6
-spec 'clocksi_interactive_coord:receive_read_objects_result'
        (cast, {ok, {key(), type(), snapshot()}}, clocksi_interactive_coord:state()) -> coord_result();
        (info, {any(), any()}, clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:receive_read_objects_result'(_, _, _) -> error(overlay).

%% the casts of clocksi_readitem:async_validate_or_read_data_item/7 for a read that worked
-spec 'clocksi_interactive_coord:receive_validate_or_read_objects_result'(
        cast,
        {ok, {invalid, key(), type(), snapshot(), object_token()} | {valid, key(), type()}},
        clocksi_interactive_coord:state()) ->
          coord_result().
'clocksi_interactive_coord:receive_validate_or_read_objects_result'(_, _, _) -> error(overlay).

%% the replies of logging_vnode to asyn_append/4, and the timeout of execute_command/4
-spec 'clocksi_interactive_coord:receive_logging_responses'
        (state_timeout, timeout, clocksi_interactive_coord:state()) -> coord_result();
        (cast, {error, term()} | {ok, op_id()} | timeout, clocksi_interactive_coord:state()) -> coord_result();
        (info, {any(), any()}, clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:receive_logging_responses'(_, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:receive_committed'
        (cast, committed, clocksi_interactive_coord:state()) -> coord_result();
        (info, {any(), any()}, clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:receive_committed'(_, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:committing_single'({call, gen_statem:from()}, commit,
                                                    clocksi_interactive_coord:state()) ->
          coord_result().
'clocksi_interactive_coord:committing_single'(_, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:code_change'(term(), atom(), clocksi_interactive_coord:state(), term()) ->
          {ok, atom(), clocksi_interactive_coord:state()}.
'clocksi_interactive_coord:code_change'(_, _, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:terminate'(term(), atom(), clocksi_interactive_coord:state()) -> ok.
'clocksi_interactive_coord:terminate'(_, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:callback_mode'() -> state_functions.
'clocksi_interactive_coord:callback_mode'() -> error(overlay).

%% answers the client and stops the process: {stop, normal, State}
-spec 'clocksi_interactive_coord:reply_to_client'(clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:reply_to_client'(_) -> error(overlay).

%% replaces the first occurrence of the key by the value read for it; error when the list does not have it
-spec 'clocksi_interactive_coord:replace_first'(list(), key(), term()) -> list() | error.
'clocksi_interactive_coord:replace_first'(_, _, _) -> error(overlay).

%% the snapshot that was read; after an error the client has its reply already
-spec 'clocksi_interactive_coord:perform_read'({key(), type()}, updated_partitions(), clocksi_interactive_coord:tx(),
                                               gen_statem:from()) ->
          snapshot() | {error, reason()}.
'clocksi_interactive_coord:perform_read'(_, _, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:perform_validate_or_read'({key(), type(), object_token()}, updated_partitions(),
                                                           clocksi_interactive_coord:tx(), gen_statem:from()) ->
          valid | {invalid, snapshot(), object_token()} | {error, reason()}.
'clocksi_interactive_coord:perform_validate_or_read'(_, _, _, _) -> error(overlay).

%% the new write sets and the client operations so far, the new one first
-spec 'clocksi_interactive_coord:perform_update'({key(), type(), op()}, updated_partitions(),
                                                 clocksi_interactive_coord:tx(), gen_statem:from(),
                                                 [{key(), type(), op()}]) ->
          {updated_partitions(), [{key(), type(), op()}]} | {error, reason()}.
'clocksi_interactive_coord:perform_update'(_, _, _, _, _) -> error(overlay).

%% WriteSet is the write set of the partition so far, [] when it has none
-spec 'clocksi_interactive_coord:append_updated_partitions'(updated_partitions(), write_set(), index_node(),
                                                            {key(), type(), effect()}) ->
          updated_partitions().
'clocksi_interactive_coord:append_updated_partitions'(_, _, _, _) -> error(overlay).

-spec 'clocksi_interactive_coord:process_prepared'(clock_time(), clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:process_prepared'(_, _) -> error(overlay).

-spec 'clocksi_interactive_coord:abort'(clocksi_interactive_coord:state()) -> coord_result().
'clocksi_interactive_coord:abort'(_) -> error(overlay).

%% the client operations of the state, #state.client_ops
-spec 'clocksi_interactive_coord:execute_post_commit_hooks'([{key(), type(), op()}]) -> ok.
'clocksi_interactive_coord:execute_post_commit_hooks'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% clocksi_interactive_coord_sup
%% ---------------------------------------------------------------------------------------------

-spec 'clocksi_interactive_coord_sup:start_link'() -> start_link_ret().
'clocksi_interactive_coord_sup:start_link'() -> error(overlay).

%% supervisor:startchild_ret(), spelled out: cure calls this function and does not refer to supervisor
-spec 'clocksi_interactive_coord_sup:start_fsm'() ->
          {ok, undefined | pid()} | {ok, undefined | pid(), term()} | {error, term()}.
'clocksi_interactive_coord_sup:start_fsm'() -> error(overlay).

-spec 'clocksi_interactive_coord_sup:init'([]) -> sup_init().
'clocksi_interactive_coord_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% clocksi_materializer
%% ---------------------------------------------------------------------------------------------

%% the arguments of materialize_intern/11, with the next operation taken out of the list or the tuple
-spec 'clocksi_materializer:materialize_intern_perform'(
        type(),
        [clocksi_materializer:clocksi_payload()],
        integer(),
        integer(),
        snapshot_time() | ignore,
        snapshot_time(),
        {integer(), clocksi_materializer:clocksi_payload()},
        [{integer(), clocksi_materializer:clocksi_payload()}] | tuple(),
        clocksi_materializer:txid() | ignore,
        snapshot_time() | ignore,
        boolean(),
        non_neg_integer()) ->
          {ok, [clocksi_materializer:clocksi_payload()], integer(), snapshot_time() | ignore, boolean()}.
'clocksi_materializer:materialize_intern_perform'(_, _, _, _, _, _, _, _, _, _, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% clocksi_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

%% the record state of clocksi_vnode, which has no type for it:
%% partition, prepared_tx, committed_tx, read_servers, prepared_dict
-type clocksi_vnode_state() :: {state, partition_id(), cache_id(), cache_id(), non_neg_integer(), list()}.

%% the pid of the vnode of a partition. logging_vnode:start_vnode/1 has a spec in the source: (integer()) -> any()
-spec 'clocksi_vnode:start_vnode'(partition_id()) -> {ok, pid()}.
'clocksi_vnode:start_vnode'(_) -> error(overlay).

%% the second argument is the transaction, although the source calls it TxId
-spec 'clocksi_vnode:read_data_item'(index_node(), clocksi_vnode:tx(), key(), type(), write_set()) ->
          {ok, snapshot()} | {error, reason()}.
'clocksi_vnode:read_data_item'(_, _, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:async_read_data_item'(index_node(), clocksi_vnode:tx(), key(), type()) -> ok.
'clocksi_vnode:async_read_data_item'(_, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:validate_or_read_data_item'(index_node(), clocksi_vnode:tx(), key(), type(), object_token(),
                                                 write_set()) ->
          {ok, valid} | {ok, {invalid, snapshot(), object_token()}} | {error, reason()}.
'clocksi_vnode:validate_or_read_data_item'(_, _, _, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:async_validate_or_read_data_item'(index_node(), clocksi_vnode:tx(), key(), type(),
                                                       object_token()) -> ok.
'clocksi_vnode:async_validate_or_read_data_item'(_, _, _, _, _) -> error(overlay).

%% the prepared transactions of the key with their prepare times, as clocksi_readitem:check_prepared_list/3 takes them
-spec 'clocksi_vnode:get_active_txns_key'(key(), partition_id()) -> {ok, [{clocksi_vnode:txid(), clock_time()}]}.
'clocksi_vnode:get_active_txns_key'(_, _) -> error(overlay).

-spec 'clocksi_vnode:send_min_prepared'(partition_id()) -> ok.
'clocksi_vnode:send_min_prepared'(_) -> error(overlay).

-spec 'clocksi_vnode:prepare'(updated_partitions(), clocksi_vnode:tx()) -> ok.
'clocksi_vnode:prepare'(_, _) -> error(overlay).

%% for a transaction that wrote to one partition
-spec 'clocksi_vnode:single_commit'(updated_partitions(), clocksi_vnode:tx()) -> ok.
'clocksi_vnode:single_commit'(_, _) -> error(overlay).

%% the replies that clocksi_interactive_coord:perform_singleitem_update/5 handles
-spec 'clocksi_vnode:single_commit_sync'(updated_partitions(), clocksi_vnode:tx()) ->
          {committed, clock_time()} | abort | {error, reason()}.
'clocksi_vnode:single_commit_sync'(_, _) -> error(overlay).

-spec 'clocksi_vnode:commit'(updated_partitions(), clocksi_vnode:tx(), clock_time()) -> ok.
'clocksi_vnode:commit'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:abort'(updated_partitions(), clocksi_vnode:tx()) -> ok.
'clocksi_vnode:abort'(_, _) -> error(overlay).

-spec 'clocksi_vnode:init'([partition_id()]) -> {ok, clocksi_vnode_state()}.
'clocksi_vnode:init'(_) -> error(overlay).

-spec 'clocksi_vnode:check_tables_ready'() -> boolean().
'clocksi_vnode:check_tables_ready'() -> error(overlay).

-spec 'clocksi_vnode:check_table_ready'([{partition_id(), node()}]) -> boolean().
'clocksi_vnode:check_table_ready'(_) -> error(overlay).

%% the last clause takes any request
-spec 'clocksi_vnode:handle_command'(term(), sender(), clocksi_vnode_state()) ->
          {reply, term(), clocksi_vnode_state()} | {noreply, clocksi_vnode_state()}.
'clocksi_vnode:handle_command'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:handle_handoff_command'(term(), sender(), clocksi_vnode_state()) -> {noreply, clocksi_vnode_state()}.
'clocksi_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:handoff_starting'(handoff_target(), clocksi_vnode_state()) -> {true, clocksi_vnode_state()}.
'clocksi_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'clocksi_vnode:handoff_cancelled'(clocksi_vnode_state()) -> {ok, clocksi_vnode_state()}.
'clocksi_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'clocksi_vnode:handoff_finished'(handoff_target(), clocksi_vnode_state()) -> {ok, clocksi_vnode_state()}.
'clocksi_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'clocksi_vnode:handle_handoff_data'(binary(), clocksi_vnode_state()) -> {reply, ok, clocksi_vnode_state()}.
'clocksi_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'clocksi_vnode:encode_handoff_item'(term(), term()) -> binary().
'clocksi_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'clocksi_vnode:is_empty'(clocksi_vnode_state()) -> {boolean(), clocksi_vnode_state()}.
'clocksi_vnode:is_empty'(_) -> error(overlay).

-spec 'clocksi_vnode:delete'(clocksi_vnode_state()) -> {ok, clocksi_vnode_state()}.
'clocksi_vnode:delete'(_) -> error(overlay).

-spec 'clocksi_vnode:handle_coverage'(term(), keyspaces(), sender(), clocksi_vnode_state()) ->
          {stop, not_implemented, clocksi_vnode_state()}.
'clocksi_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:handle_exit'(pid(), term(), clocksi_vnode_state()) -> {noreply, clocksi_vnode_state()}.
'clocksi_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:terminate'(term(), clocksi_vnode_state()) -> ok.
'clocksi_vnode:terminate'(_, _) -> error(overlay).

-spec 'clocksi_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'clocksi_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'clocksi_vnode:handle_overload_info'(_, _) -> error(overlay).

%% The result of logging the prepare record, or the error no_updates or write_conflict; the prepare
%% time, 0 after an error; the prepared transactions by prepare time, list() as #state.prepared_dict,
%% get_min_prep/1 and get_time/2 say it.
-spec 'clocksi_vnode:prepare'(clocksi_vnode:tx(), write_set(), cache_id(), cache_id(), clock_time(), list()) ->
          {{ok, op_id()} | {error, reason()}, clock_time(), list()}.
'clocksi_vnode:prepare'(_, _, _, _, _, _) -> error(overlay).

%% the dict collects, per key, the transactions that were prepared for it before
-spec 'clocksi_vnode:set_prepared'(cache_id(), write_set(), clocksi_vnode:txid(), clock_time(), dict:dict()) -> dict:dict().
'clocksi_vnode:set_prepared'(_, _, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:reset_prepared'(cache_id(), write_set(), clocksi_vnode:txid(), clock_time(), dict:dict()) -> ok.
'clocksi_vnode:reset_prepared'(_, _, _, _, _) -> error(overlay).

%% the list is the new #state.prepared_dict
-spec 'clocksi_vnode:commit'(clocksi_vnode:tx(), clock_time(), write_set(), cache_id(), clocksi_vnode_state()) ->
          {ok, committed, list()} | {error, materializer_failure | timeout | no_updates}.
'clocksi_vnode:commit'(_, _, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:clean_and_notify'(clocksi_vnode:txid(), write_set(), clocksi_vnode_state()) -> list().
'clocksi_vnode:clean_and_notify'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:clean_prepared'(cache_id(), write_set(), clocksi_vnode:txid()) -> ok.
'clocksi_vnode:clean_prepared'(_, _, _) -> error(overlay).

-spec 'clocksi_vnode:now_microsec'(erlang:timestamp()) -> non_neg_integer().
'clocksi_vnode:now_microsec'(_) -> error(overlay).

-spec 'clocksi_vnode:certification_check'(clocksi_vnode:tx(), write_set(), cache_id(), cache_id()) -> boolean().
'clocksi_vnode:certification_check'(_, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:certification_with_check'(clocksi_vnode:txid(), write_set(), cache_id(), cache_id()) -> boolean().
'clocksi_vnode:certification_with_check'(_, _, _, _) -> error(overlay).

-spec 'clocksi_vnode:check_prepared'(clocksi_vnode:txid(), cache_id(), key()) -> boolean().
'clocksi_vnode:check_prepared'(_, _, _) -> error(overlay).

%% the effects on the key, the last one first
-spec 'clocksi_vnode:reverse_and_filter_updates_per_key'(write_set(), key()) -> [effect()].
'clocksi_vnode:reverse_and_filter_updates_per_key'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% cure
%% ---------------------------------------------------------------------------------------------

%% as read_objects/3 in the source
-spec 'cure:get_objects'(snapshot_time() | ignore, txn_properties(), [bound_object()]) ->
          {ok, list(), vectorclock()} | {error, reason()}.
'cure:get_objects'(_, _, _) -> error(overlay).

%% the states that were read, or their values
-spec 'cure:transform_reads'([snapshot()], object_value | object_state, [bound_object()]) -> [term()].
'cure:transform_reads'(_, _, _) -> error(overlay).

%% as the result of validate_or_read_objects/3 in the source
-spec 'cure:transform_reads_from_validate_or_reads'([valid | {invalid, snapshot(), object_token()}], [bound_object()]) ->
          [valid | {invalid, term(), binary()}].
'cure:transform_reads_from_validate_or_reads'(_, _) -> error(overlay).

-spec 'cure:format_read_params'([bound_object()]) -> [{{key(), bucket()}, type()}].
'cure:format_read_params'(_) -> error(overlay).

-spec 'cure:format_update_params'([{bound_object(), op_name(), op_param()}]) -> [{{key(), bucket()}, type(), op()}].
'cure:format_update_params'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_dep_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_dep_vnode:start_vnode'(partition_id()) -> {ok, pid()}.
'inter_dc_dep_vnode:start_vnode'(_) -> error(overlay).

%% the fun of the fold over the DCs in process_all_queues/1: the state and the number of stored transactions
-spec 'inter_dc_dep_vnode:process_queue'(dcid(), {inter_dc_dep_vnode:state(), non_neg_integer()}) ->
          {inter_dc_dep_vnode:state(), non_neg_integer()}.
'inter_dc_dep_vnode:process_queue'(_, _) -> error(overlay).

%% the three requests, no clause for others
-spec 'inter_dc_dep_vnode:handle_command'(
        {set_dependency_clock, vectorclock()} | {txn, inter_dc_dep_vnode:interdc_txn()} | {drop_ping, boolean()},
        sender(), inter_dc_dep_vnode:state()) ->
          {reply, ok, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handle_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_coverage'(term(), keyspaces(), sender(), inter_dc_dep_vnode:state()) ->
          {stop, not_implemented, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_exit'(pid(), term(), inter_dc_dep_vnode:state()) -> {noreply, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handoff_starting'(handoff_target(), inter_dc_dep_vnode:state()) ->
          {true, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handoff_cancelled'(inter_dc_dep_vnode:state()) -> {ok, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'inter_dc_dep_vnode:handoff_finished'(handoff_target(), inter_dc_dep_vnode:state()) ->
          {ok, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_handoff_command'(term(), sender(), inter_dc_dep_vnode:state()) ->
          {noreply, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_handoff_data'(binary(), inter_dc_dep_vnode:state()) ->
          {reply, ok, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:encode_handoff_item'(term(), term()) -> binary().
'inter_dc_dep_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:is_empty'(inter_dc_dep_vnode:state()) -> {boolean(), inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:is_empty'(_) -> error(overlay).

-spec 'inter_dc_dep_vnode:terminate'(term(), inter_dc_dep_vnode:state()) -> ok.
'inter_dc_dep_vnode:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:delete'(inter_dc_dep_vnode:state()) -> {ok, inter_dc_dep_vnode:state()}.
'inter_dc_dep_vnode:delete'(_) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'inter_dc_dep_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'inter_dc_dep_vnode:handle_overload_info'(_, _) -> error(overlay).

-spec 'inter_dc_dep_vnode:pop_txn'(inter_dc_dep_vnode:state(), dcid()) -> inter_dc_dep_vnode:state().
'inter_dc_dep_vnode:pop_txn'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_log_sender_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_log_sender_vnode:start_vnode'(partition_id()) -> {ok, pid()}.
'inter_dc_log_sender_vnode:start_vnode'(_) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:init'([partition_id()]) -> {ok, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:init'(_) -> error(overlay).

%% the requests of the API functions, {hello} of dc_utilities and ping of the timer; no clause for others
-spec 'inter_dc_log_sender_vnode:handle_command'(
        {start_timer} | {update_last_log_id, inter_dc_log_sender_vnode:op_number()} |
        {log_event, inter_dc_log_sender_vnode:log_record()} | {stable_time, non_neg_integer()} | {hello} | ping,
        sender(), inter_dc_log_sender_vnode:state()) ->
          {reply, ok, inter_dc_log_sender_vnode:state()} | {noreply, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handle_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_coverage'(term(), keyspaces(), sender(), inter_dc_log_sender_vnode:state()) ->
          {stop, not_implemented, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_exit'(pid(), term(), inter_dc_log_sender_vnode:state()) ->
          {noreply, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handoff_starting'(handoff_dest(), inter_dc_log_sender_vnode:state()) ->
          {true, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handoff_cancelled'(inter_dc_log_sender_vnode:state()) ->
          {ok, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handoff_finished'(handoff_dest(), inter_dc_log_sender_vnode:state()) ->
          {ok, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_handoff_command'(term(), sender(), inter_dc_log_sender_vnode:state()) ->
          {noreply, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_handoff_data'(binary(), inter_dc_log_sender_vnode:state()) ->
          {reply, ok, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:encode_handoff_item'(term(), term()) -> binary().
'inter_dc_log_sender_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:is_empty'(inter_dc_log_sender_vnode:state()) ->
          {boolean(), inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:is_empty'(_) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:delete'(inter_dc_log_sender_vnode:state()) -> {ok, inter_dc_log_sender_vnode:state()}.
'inter_dc_log_sender_vnode:delete'(_) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:terminate'(term(), inter_dc_log_sender_vnode:state()) -> ok.
'inter_dc_log_sender_vnode:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'inter_dc_log_sender_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_log_sender_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'inter_dc_log_sender_vnode:handle_overload_info'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_manager
%% ---------------------------------------------------------------------------------------------

%% waits until the stable snapshot has a time of the DC above MinValue
-spec 'inter_dc_manager:wait_for_stable_snapshot'(dcid(), non_neg_integer()) -> ok.
'inter_dc_manager:wait_for_stable_snapshot'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_pub: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_pub:start_link'() -> start_link_ret().
'inter_dc_pub:start_link'() -> error(overlay).

%% the one request, of broadcast/1
-spec 'inter_dc_pub:handle_call'({publish, binary()}, gen_server:from(), inter_dc_pub:state()) ->
          {reply, ok, inter_dc_pub:state()}.
'inter_dc_pub:handle_call'(_, _, _) -> error(overlay).

-spec 'inter_dc_pub:terminate'(term(), inter_dc_pub:state()) -> ok.
'inter_dc_pub:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_pub:handle_cast'(term(), inter_dc_pub:state()) -> {noreply, inter_dc_pub:state()}.
'inter_dc_pub:handle_cast'(_, _) -> error(overlay).

-spec 'inter_dc_pub:handle_info'(term(), inter_dc_pub:state()) -> {noreply, inter_dc_pub:state()}.
'inter_dc_pub:handle_info'(_, _) -> error(overlay).

-spec 'inter_dc_pub:code_change'(term(), inter_dc_pub:state(), term()) -> {ok, inter_dc_pub:state()}.
'inter_dc_pub:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_query_dealer: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_query_dealer:start_link'() -> start_link_ret().
'inter_dc_query_dealer:start_link'() -> error(overlay).

%% The requests of perform_request/4, add_dc/2 and del_dc/1, no clause for others. The log readers
%% of a DC are, per node, the partitions of the node and its addresses, what
%% inter_dc_query_router:get_address_list/0 gives: the clause for add_dc takes them apart so. add_dc/2
%% and the record descriptor say [socket_address()].
-spec 'inter_dc_query_dealer:handle_call'(
        {any_request, inter_dc_message_type(), pdcid(), binary(), fun((binary()) -> ok)} |
        {add_dc, dcid(), [{[partition_id()], [socket_address()]}]} |
        {del_dc, dcid()},
        gen_server:from(), inter_dc_query_dealer:state()) ->
          {reply, ok | unknown_dc, inter_dc_query_dealer:state()}.
'inter_dc_query_dealer:handle_call'(_, _, _) -> error(overlay).

%% the answers of the sockets come as {zmq, Socket, Binary, Flags}; the last clause takes any message
-spec 'inter_dc_query_dealer:handle_info'(term(), inter_dc_query_dealer:state()) -> {noreply, inter_dc_query_dealer:state()}.
'inter_dc_query_dealer:handle_info'(_, _) -> error(overlay).

-spec 'inter_dc_query_dealer:terminate'(term(), inter_dc_query_dealer:state()) -> ok.
'inter_dc_query_dealer:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_query_dealer:handle_cast'(term(), inter_dc_query_dealer:state()) -> {noreply, inter_dc_query_dealer:state()}.
'inter_dc_query_dealer:handle_cast'(_, _) -> error(overlay).

-spec 'inter_dc_query_dealer:code_change'(term(), inter_dc_query_dealer:state(), term()) ->
          {ok, inter_dc_query_dealer:state()}.
'inter_dc_query_dealer:code_change'(_, _, _) -> error(overlay).

%% remembers the request under its id and counts the id up
-spec 'inter_dc_query_dealer:req_sent'(binary(), inter_dc_query_dealer:request_cache_entry(),
                                       inter_dc_query_dealer:state()) ->
          inter_dc_query_dealer:state().
'inter_dc_query_dealer:req_sent'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_query_response: a gen_server
%% ---------------------------------------------------------------------------------------------

%% the casts of get_entries/2 and request_permissions/2; the last clause takes any message
-spec 'inter_dc_query_response:handle_cast'(term(), inter_dc_query_response:state()) ->
          {noreply, inter_dc_query_response:state()}.
'inter_dc_query_response:handle_cast'(_, _) -> error(overlay).

-spec 'inter_dc_query_response:handle_call'(term(), gen_server:from(), inter_dc_query_response:state()) ->
          {reply, error, inter_dc_query_response:state()}.
'inter_dc_query_response:handle_call'(_, _, _) -> error(overlay).

-spec 'inter_dc_query_response:handle_info'(term(), inter_dc_query_response:state()) ->
          {noreply, inter_dc_query_response:state()}.
'inter_dc_query_response:handle_info'(_, _) -> error(overlay).

-spec 'inter_dc_query_response:terminate'(term(), inter_dc_query_response:state()) -> ok.
'inter_dc_query_response:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_query_response:code_change'(term(), inter_dc_query_response:state(), term()) ->
          {ok, inter_dc_query_response:state()}.
'inter_dc_query_response:code_change'(_, _, _) -> error(overlay).

%% the registered name of the n-th server, as start_link/1 says it for the number
-spec 'inter_dc_query_response:generate_server_name'(non_neg_integer()) -> atom().
'inter_dc_query_response:generate_server_name'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_query_response_sup
%% ---------------------------------------------------------------------------------------------

%% the number of servers, ?INTER_DC_QUERY_CONCURRENCY
-spec 'inter_dc_query_response_sup:start_link'(non_neg_integer()) -> start_link_ret().
'inter_dc_query_response_sup:start_link'(_) -> error(overlay).

-spec 'inter_dc_query_response_sup:generate_module_name'(non_neg_integer()) -> atom().
'inter_dc_query_response_sup:generate_module_name'(_) -> error(overlay).

-spec 'inter_dc_query_response_sup:generate_worker_spec'(non_neg_integer()) -> supervisor:child_spec().
'inter_dc_query_response_sup:generate_worker_spec'(_) -> error(overlay).

-spec 'inter_dc_query_response_sup:init'(non_neg_integer()) -> sup_init().
'inter_dc_query_response_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_query_router: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_query_router:start_link'() -> start_link_ret().
'inter_dc_query_router:start_link'() -> error(overlay).

%% the parts of a request come as {zmq, Socket, Binary, Flags}; the last clause takes any message
-spec 'inter_dc_query_router:handle_info'(term(), inter_dc_query_router:state()) -> {noreply, inter_dc_query_router:state()}.
'inter_dc_query_router:handle_info'(_, _) -> error(overlay).

%% no call is answered
-spec 'inter_dc_query_router:handle_call'(term(), gen_server:from(), inter_dc_query_router:state()) ->
          {noreply, inter_dc_query_router:state()}.
'inter_dc_query_router:handle_call'(_, _, _) -> error(overlay).

-spec 'inter_dc_query_router:terminate'(term(), inter_dc_query_router:state()) -> ok.
'inter_dc_query_router:terminate'(_, _) -> error(overlay).

%% the cast of send_response/2; the last clause takes any message
-spec 'inter_dc_query_router:handle_cast'(term(), inter_dc_query_router:state()) -> {noreply, inter_dc_query_router:state()}.
'inter_dc_query_router:handle_cast'(_, _) -> error(overlay).

-spec 'inter_dc_query_router:code_change'(term(), inter_dc_query_router:state(), term()) ->
          {ok, inter_dc_query_router:state()}.
'inter_dc_query_router:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_sub: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_sub:start_link'() -> start_link_ret().
'inter_dc_sub:start_link'() -> error(overlay).

%% the requests of add_dc/2 and del_dc/1 with the types of their specs, no clause for others
-spec 'inter_dc_sub:handle_call'({add_dc, dcid(), [socket_address()]} | {del_dc, dcid()}, gen_server:from(),
                                 inter_dc_sub:state()) ->
          {reply, ok | error, inter_dc_sub:state()}.
'inter_dc_sub:handle_call'(_, _, _) -> error(overlay).

%% a transaction from a subscribed socket, no clause for other messages
-spec 'inter_dc_sub:handle_info'({zmq, zmq_socket(), binary(), list()}, inter_dc_sub:state()) -> {noreply, inter_dc_sub:state()}.
'inter_dc_sub:handle_info'(_, _) -> error(overlay).

-spec 'inter_dc_sub:handle_cast'(term(), inter_dc_sub:state()) -> {noreply, inter_dc_sub:state()}.
'inter_dc_sub:handle_cast'(_, _) -> error(overlay).

-spec 'inter_dc_sub:code_change'(term(), inter_dc_sub:state(), term()) -> {ok, inter_dc_sub:state()}.
'inter_dc_sub:code_change'(_, _, _) -> error(overlay).

-spec 'inter_dc_sub:terminate'(term(), inter_dc_sub:state()) -> ok.
'inter_dc_sub:terminate'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_sub_buf
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_sub_buf:process_queue'(inter_dc_sub_buf:inter_dc_sub_buf()) -> inter_dc_sub_buf:inter_dc_sub_buf().
'inter_dc_sub_buf:process_queue'(_) -> error(overlay).

%% compares the opid before a transaction with the last one that was seen
-spec 'inter_dc_sub_buf:cmp'(non_neg_integer(), non_neg_integer()) -> gt | lt | eq.
'inter_dc_sub_buf:cmp'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_sub_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_sub_vnode:init'([partition_id()]) -> {ok, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:init'(_) -> error(overlay).

-spec 'inter_dc_sub_vnode:start_vnode'(partition_id()) -> {ok, pid()}.
'inter_dc_sub_vnode:start_vnode'(_) -> error(overlay).

%% the two requests of call/2, no clause for others
-spec 'inter_dc_sub_vnode:handle_command'({txn, inter_dc_sub_vnode:interdc_txn()} | {log_reader_resp, binary()},
                                          sender(), inter_dc_sub_vnode:state()) ->
          {noreply, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handle_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_coverage'(term(), keyspaces(), sender(), inter_dc_sub_vnode:state()) ->
          {stop, not_implemented, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_exit'(pid(), term(), inter_dc_sub_vnode:state()) -> {noreply, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handoff_starting'(handoff_target(), inter_dc_sub_vnode:state()) ->
          {true, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handoff_cancelled'(inter_dc_sub_vnode:state()) -> {ok, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'inter_dc_sub_vnode:handoff_finished'(handoff_target(), inter_dc_sub_vnode:state()) ->
          {ok, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_handoff_command'(term(), sender(), inter_dc_sub_vnode:state()) ->
          {noreply, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_handoff_data'(binary(), inter_dc_sub_vnode:state()) ->
          {reply, ok, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:encode_handoff_item'(term(), term()) -> binary().
'inter_dc_sub_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:is_empty'(inter_dc_sub_vnode:state()) -> {boolean(), inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:is_empty'(_) -> error(overlay).

-spec 'inter_dc_sub_vnode:terminate'(term(), inter_dc_sub_vnode:state()) -> ok.
'inter_dc_sub_vnode:terminate'(_, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:delete'(inter_dc_sub_vnode:state()) -> {ok, inter_dc_sub_vnode:state()}.
'inter_dc_sub_vnode:delete'(_) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'inter_dc_sub_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'inter_dc_sub_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'inter_dc_sub_vnode:handle_overload_info'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% inter_dc_sup
%% ---------------------------------------------------------------------------------------------

-spec 'inter_dc_sup:start_link'() -> start_link_ret().
'inter_dc_sup:start_link'() -> error(overlay).

-spec 'inter_dc_sup:init'([]) -> sup_init().
'inter_dc_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% logging_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

%% the record state of logging_vnode, which has no type for it: partition, logs_map, enable_log_to_disk,
%% op_id_table, recovered_vector, senders_awaiting_ack, last_read_map
-type logging_vnode_state() ::
        {state, partition_id(), dict:dict(log_id(), logging_vnode:disklog()), boolean(), cache_id(), vectorclock(),
         dict:dict(log_id(), sender()), dict:dict(log_id(), {log_opid(), disk_log:continuation()})}.

%% {error, Reason} when a log cannot be opened
-spec 'logging_vnode:init'([partition_id()]) -> {ok, logging_vnode_state()} | {error, reason()}.
'logging_vnode:init'(_) -> error(overlay).

%% the last clause takes any request
-spec 'logging_vnode:handle_command'(term(), sender(), logging_vnode_state()) ->
          {reply, term(), logging_vnode_state()} | {noreply, logging_vnode_state()}.
'logging_vnode:handle_command'(_, _, _) -> error(overlay).

%% undefined for no bound, as get_ops_from_log/8 and handle_commit/8 have it
-spec 'logging_vnode:check_min_time'(snapshot_time(), snapshot_time() | undefined) -> boolean().
'logging_vnode:check_min_time'(_, _) -> error(overlay).

-spec 'logging_vnode:check_max_time'(snapshot_time(), snapshot_time() | undefined) -> boolean().
'logging_vnode:check_max_time'(_, _) -> error(overlay).

%% a fold request gives the folded value as the reply; any other command is ignored
-spec 'logging_vnode:handle_handoff_command'(term(), sender(), logging_vnode_state()) ->
          {reply, term(), logging_vnode_state()} | {noreply, logging_vnode_state()}.
'logging_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'logging_vnode:encode_handoff_item'(term(), term()) -> binary().
'logging_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'logging_vnode:handoff_starting'(handoff_dest(), logging_vnode_state()) -> {true, logging_vnode_state()}.
'logging_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'logging_vnode:handoff_cancelled'(logging_vnode_state()) -> {ok, logging_vnode_state()}.
'logging_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'logging_vnode:handoff_finished'(handoff_dest(), logging_vnode_state()) -> {ok, logging_vnode_state()}.
'logging_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'logging_vnode:handle_handoff_data'(binary(), logging_vnode_state()) ->
          {reply, ok | {error, reason()}, logging_vnode_state()}.
'logging_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'logging_vnode:is_empty'(logging_vnode_state()) -> {boolean(), logging_vnode_state()}.
'logging_vnode:is_empty'(_) -> error(overlay).

-spec 'logging_vnode:delete'(logging_vnode_state()) -> {ok, logging_vnode_state()}.
'logging_vnode:delete'(_) -> error(overlay).

%% the one message, no clause for others; nothing in antidote sends it
-spec 'logging_vnode:handle_info'({sync, logging_vnode:disklog(), log_id()}, logging_vnode_state()) ->
          {ok, logging_vnode_state()}.
'logging_vnode:handle_info'(_, _) -> error(overlay).

-spec 'logging_vnode:handle_coverage'(term(), keyspaces(), sender(), logging_vnode_state()) ->
          {stop, not_implemented, logging_vnode_state()}.
'logging_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'logging_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'logging_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'logging_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'logging_vnode:handle_overload_info'(_, _) -> error(overlay).

-spec 'logging_vnode:handle_exit'(pid(), term(), logging_vnode_state()) -> {noreply, logging_vnode_state()}.
'logging_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'logging_vnode:terminate'(term(), logging_vnode_state()) -> ok.
'logging_vnode:terminate'(_, _) -> error(overlay).

%% the log, the fun and the accumulator as join_logs/3 in the source has them
-spec 'logging_vnode:fold_log'(log(), start | disk_log:continuation(), fun(), term()) -> term().
'logging_vnode:fold_log'(_, _, _, _) -> error(overlay).

%% the setting data_dir of antidote, "data" without it
-spec 'logging_vnode:data_dir'() -> string().
'logging_vnode:data_dir'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% materializer_vnode: a riak_core_vnode
%% ---------------------------------------------------------------------------------------------

-spec 'materializer_vnode:start_vnode'(partition_id()) -> {ok, pid()}.
'materializer_vnode:start_vnode'(_) -> error(overlay).

-spec 'materializer_vnode:init'([partition_id()]) -> {ok, materializer_vnode:state()}.
'materializer_vnode:init'(_) -> error(overlay).

%% the last clause takes any request
-spec 'materializer_vnode:handle_command'(term(), sender(), materializer_vnode:state()) ->
          {reply, term(), materializer_vnode:state()} | {noreply, materializer_vnode:state()}.
'materializer_vnode:handle_command'(_, _, _) -> error(overlay).

%% a fold request gives the folded value as the reply; any other command is ignored
-spec 'materializer_vnode:handle_handoff_command'(term(), sender(), materializer_vnode:state()) ->
          {reply, term(), materializer_vnode:state()} | {noreply, materializer_vnode:state()}.
'materializer_vnode:handle_handoff_command'(_, _, _) -> error(overlay).

-spec 'materializer_vnode:handoff_starting'(handoff_dest(), materializer_vnode:state()) ->
          {true, materializer_vnode:state()}.
'materializer_vnode:handoff_starting'(_, _) -> error(overlay).

-spec 'materializer_vnode:handoff_cancelled'(materializer_vnode:state()) -> {ok, materializer_vnode:state()}.
'materializer_vnode:handoff_cancelled'(_) -> error(overlay).

-spec 'materializer_vnode:handoff_finished'(handoff_dest(), materializer_vnode:state()) ->
          {ok, materializer_vnode:state()}.
'materializer_vnode:handoff_finished'(_, _) -> error(overlay).

-spec 'materializer_vnode:handle_handoff_data'(binary(), materializer_vnode:state()) ->
          {reply, ok, materializer_vnode:state()}.
'materializer_vnode:handle_handoff_data'(_, _) -> error(overlay).

-spec 'materializer_vnode:encode_handoff_item'(term(), term()) -> binary().
'materializer_vnode:encode_handoff_item'(_, _) -> error(overlay).

-spec 'materializer_vnode:is_empty'(materializer_vnode:state()) -> {boolean(), materializer_vnode:state()}.
'materializer_vnode:is_empty'(_) -> error(overlay).

-spec 'materializer_vnode:delete'(materializer_vnode:state()) -> {ok, materializer_vnode:state()}.
'materializer_vnode:delete'(_) -> error(overlay).

-spec 'materializer_vnode:handle_coverage'(term(), keyspaces(), sender(), materializer_vnode:state()) ->
          {stop, not_implemented, materializer_vnode:state()}.
'materializer_vnode:handle_coverage'(_, _, _, _) -> error(overlay).

-spec 'materializer_vnode:handle_overload_command'(term(), sender(), partition_id()) -> ok.
'materializer_vnode:handle_overload_command'(_, _, _) -> error(overlay).

-spec 'materializer_vnode:handle_overload_info'(term(), partition_id()) -> ok.
'materializer_vnode:handle_overload_info'(_, _) -> error(overlay).

-spec 'materializer_vnode:handle_exit'(pid(), term(), materializer_vnode:state()) -> {noreply, materializer_vnode:state()}.
'materializer_vnode:handle_exit'(_, _, _) -> error(overlay).

-spec 'materializer_vnode:terminate'(term(), materializer_vnode:state()) -> ok.
'materializer_vnode:terminate'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% meta_data_manager: a gen_server
%% ---------------------------------------------------------------------------------------------

%% the casts of send_meta_data/4, add_node/3 and remove_node/2; the last clause takes any message
-spec 'meta_data_manager:handle_cast'(term(), meta_data_manager:state()) -> {noreply, meta_data_manager:state()}.
'meta_data_manager:handle_cast'(_, _) -> error(overlay).

-spec 'meta_data_manager:handle_call'(term(), gen_server:from(), meta_data_manager:state()) ->
          {reply, error, meta_data_manager:state()}.
'meta_data_manager:handle_call'(_, _, _) -> error(overlay).

-spec 'meta_data_manager:handle_info'(term(), meta_data_manager:state()) -> {noreply, meta_data_manager:state()}.
'meta_data_manager:handle_info'(_, _) -> error(overlay).

-spec 'meta_data_manager:terminate'(term(), meta_data_manager:state()) -> ok.
'meta_data_manager:terminate'(_, _) -> error(overlay).

-spec 'meta_data_manager:code_change'(term(), meta_data_manager:state(), term()) -> {ok, meta_data_manager:state()}.
'meta_data_manager:code_change'(_, _, _) -> error(overlay).

%% the global name of the manager of a kind of meta data on a node; the node as an atom(), as the
%% specs of send_meta_data/4, add_node/3 and remove_node/2 say it
-spec 'meta_data_manager:generate_server_name'(atom(), atom()) -> atom().
'meta_data_manager:generate_server_name'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% meta_data_manager_sup
%% ---------------------------------------------------------------------------------------------

%% the name of the meta data, stable_time_functions
-spec 'meta_data_manager_sup:start_link'(atom()) -> start_link_ret().
'meta_data_manager_sup:start_link'(_) -> error(overlay).

%% the argument of supervisor:start_child/2; no caller in antidote
-spec 'meta_data_manager_sup:start_fsm'(supervisor:child_spec() | [term()]) -> supervisor:startchild_ret().
'meta_data_manager_sup:start_fsm'(_) -> error(overlay).

-spec 'meta_data_manager_sup:init'(atom()) -> sup_init().
'meta_data_manager_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% meta_data_sender: a gen_statem with the one state send_meta_data
%% ---------------------------------------------------------------------------------------------

-spec 'meta_data_sender:send_meta_data'
        ({call, gen_statem:from()}, start, meta_data_sender:state()) ->
          gen_statem:event_handler_result(atom(), meta_data_sender:state());
        (state_timeout | cast, timeout, meta_data_sender:state()) ->
          gen_statem:event_handler_result(atom(), meta_data_sender:state()).
'meta_data_sender:send_meta_data'(_, _, _) -> error(overlay).

-spec 'meta_data_sender:callback_mode'() -> state_functions.
'meta_data_sender:callback_mode'() -> error(overlay).

-spec 'meta_data_sender:code_change'(term(), atom(), meta_data_sender:state(), term()) ->
          {ok, atom(), meta_data_sender:state()}.
'meta_data_sender:code_change'(_, _, _, _) -> error(overlay).

-spec 'meta_data_sender:terminate'(term(), atom(), meta_data_sender:state()) -> ok.
'meta_data_sender:terminate'(_, _, _) -> error(overlay).

%% the other ready members of the ring
-spec 'meta_data_sender:get_node_list'(riak_core_ring:riak_core_ring()) -> [node()].
'meta_data_sender:get_node_list'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% meta_data_sender_sup
%% ---------------------------------------------------------------------------------------------

%% the arguments of meta_data_sender:start_link/1: [stable_time_functions]
-spec 'meta_data_sender_sup:start_link'([atom()]) -> start_link_ret().
'meta_data_sender_sup:start_link'(_) -> error(overlay).

%% the argument of supervisor:start_child/2; no caller in antidote
-spec 'meta_data_sender_sup:start_fsm'(supervisor:child_spec() | [term()]) -> supervisor:startchild_ret().
'meta_data_sender_sup:start_fsm'(_) -> error(overlay).

-spec 'meta_data_sender_sup:init'([atom()]) -> sup_init().
'meta_data_sender_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% stable_meta_data_server: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'stable_meta_data_server:handle_cast'(term(), stable_meta_data_server:state()) ->
          {noreply, stable_meta_data_server:state()}.
'stable_meta_data_server:handle_cast'(_, _) -> error(overlay).

%% the requests of the broadcast functions and of the servers among themselves, answered with ok; the
%% last clause answers any other request with error
-spec 'stable_meta_data_server:handle_call'(term(), gen_server:from(), stable_meta_data_server:state()) ->
          {reply, ok | error, stable_meta_data_server:state()}.
'stable_meta_data_server:handle_call'(_, _, _) -> error(overlay).

-spec 'stable_meta_data_server:handle_info'(term(), stable_meta_data_server:state()) ->
          {noreply, stable_meta_data_server:state()}.
'stable_meta_data_server:handle_info'(_, _) -> error(overlay).

-spec 'stable_meta_data_server:terminate'(term(), stable_meta_data_server:state()) -> ok.
'stable_meta_data_server:terminate'(_, _) -> error(overlay).

-spec 'stable_meta_data_server:code_change'(term(), stable_meta_data_server:state(), term()) ->
          {ok, stable_meta_data_server:state()}.
'stable_meta_data_server:code_change'(_, _, _) -> error(overlay).

%% the global name of the server of a node
-spec 'stable_meta_data_server:generate_server_name'(node()) -> atom().
'stable_meta_data_server:generate_server_name'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% stable_time_functions: the meta data that meta_data_sender is started with; vector clocks
%% ---------------------------------------------------------------------------------------------

-spec 'stable_time_functions:default'() -> vectorclock().
'stable_time_functions:default'() -> error(overlay).

-spec 'stable_time_functions:initial_merged'() -> vectorclock().
'stable_time_functions:initial_merged'() -> error(overlay).

-spec 'stable_time_functions:initial_local'() -> vectorclock().
'stable_time_functions:initial_local'() -> error(overlay).

%% fold/3, lookup/2 and store/3 are vectorclock:fold/3, get/2 and set/3, with the types of their specs
-spec 'stable_time_functions:fold'(fun((term(), pos_integer(), X) -> X), X, vectorclock()) -> X.
'stable_time_functions:fold'(_, _, _) -> error(overlay).

-spec 'stable_time_functions:lookup'(term(), vectorclock()) -> non_neg_integer().
'stable_time_functions:lookup'(_, _) -> error(overlay).

-spec 'stable_time_functions:store'(term(), non_neg_integer(), vectorclock()) -> vectorclock().
'stable_time_functions:store'(_, _, _) -> error(overlay).

%% as merge/1 in the source says it: map()
-spec 'stable_time_functions:all_defined'(map()) -> boolean().
'stable_time_functions:all_defined'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% zmq_context: a gen_server
%% ---------------------------------------------------------------------------------------------

-spec 'zmq_context:start_link'() -> start_link_ret().
'zmq_context:start_link'() -> error(overlay).

%% the one request, of get/0
-spec 'zmq_context:handle_call'(get_context, gen_server:from(), zmq_context:state()) ->
          {reply, erlzmq:erlzmq_context(), zmq_context:state()}.
'zmq_context:handle_call'(_, _, _) -> error(overlay).

-spec 'zmq_context:handle_cast'(term(), zmq_context:state()) -> {noreply, zmq_context:state()}.
'zmq_context:handle_cast'(_, _) -> error(overlay).

-spec 'zmq_context:handle_info'(term(), zmq_context:state()) -> {noreply, zmq_context:state()}.
'zmq_context:handle_info'(_, _) -> error(overlay).

%% the result of erlzmq:term/1
-spec 'zmq_context:terminate'(term(), zmq_context:state()) -> ok | erlzmq:erlzmq_error().
'zmq_context:terminate'(_, _) -> error(overlay).

-spec 'zmq_context:code_change'(term(), zmq_context:state(), term()) -> {ok, zmq_context:state()}.
'zmq_context:code_change'(_, _, _) -> error(overlay).

-spec 'zmq_context:get'() -> erlzmq:erlzmq_context().
'zmq_context:get'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% zmq_utils
%% ---------------------------------------------------------------------------------------------

%% erlzmq:erlzmq_socket() and erlzmq:erlzmq_error(), spelled out: inter_dc_utils calls close_socket/1
%% and does not refer to erlzmq
-type zmq_utils_socket() :: {pos_integer(), binary()}.
-type zmq_utils_error() :: {error, atom() | {unknown, integer()}}.

%% the kinds of socket that antidote opens, of erlzmq:erlzmq_socket_type(); throws
%% failed_to_create_zmq_socket
-spec 'zmq_utils:create_socket'(pub | sub | req | xrep, boolean()) -> zmq_utils_socket().
'zmq_utils:create_socket'(_, _) -> error(overlay).

-spec 'zmq_utils:create_connect_socket'(sub | req, boolean(), socket_address()) -> zmq_utils_socket().
'zmq_utils:create_connect_socket'(_, _, _) -> error(overlay).

-spec 'zmq_utils:create_bind_socket'(pub | xrep, boolean(), inet:port_number()) -> zmq_utils_socket().
'zmq_utils:create_bind_socket'(_, _, _) -> error(overlay).

%% "*" for the address to bind to any interface
-spec 'zmq_utils:connection_string'({inet:ip_address() | string(), inet:port_number()}) -> string().
'zmq_utils:connection_string'(_) -> error(overlay).

-spec 'zmq_utils:sub_filter'(zmq_utils_socket(), binary()) -> ok | zmq_utils_error().
'zmq_utils:sub_filter'(_, _) -> error(overlay).

-spec 'zmq_utils:close_socket'(zmq_utils_socket()) -> ok | zmq_utils_error().
'zmq_utils:close_socket'(_) -> error(overlay).
