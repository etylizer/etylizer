%% A spec for each of the 882 functions of riak_core_lite 0.10.1 that have none in the source
%% (riak_core_lite case study). Records cannot be named here: a helper type that is a tuple stands for
%% the record of a module that has no type for it, with the field types of the declaration.
-module(overlay_riak_core_lite).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% ---------------------------------------------------------------------------------------------
%% chash
%% ---------------------------------------------------------------------------------------------

%% key_of/1 gives the result as an index(): crypto:hash(sha, _) has 160 bits
-spec 'chash:sha'(binary()) -> chash:index().
'chash:sha'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% chashbin
%% ---------------------------------------------------------------------------------------------

%% the result is the pos of an iterator
-spec 'chashbin:index_position'(chashbin:chash_key(), chashbin:chashbin()) -> non_neg_integer().
'chashbin:index_position'(_, _) -> error(overlay).

-spec 'chashbin:exact_iterator'(chashbin:chash_key(), chashbin:chashbin()) -> chashbin:iterator().
'chashbin:exact_iterator'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% vclock
%% ---------------------------------------------------------------------------------------------

%% the bucket properties that prune/3 reads: small_vclock, young_vclock, big_vclock, old_vclock.
%% prune/3 says BucketProps :: term() and hands it to get_property/2, which wants a list of pairs.
-type vclock_props() :: [{atom(), term()}].

-spec 'vclock:merge'([vclock:vclock()], vclock:vclock()) -> vclock:vclock().
'vclock:merge'(_, _) -> error(overlay).

-spec 'vclock:merge'(vclock:vclock(), vclock:vclock(), vclock:vclock()) -> vclock:vclock().
'vclock:merge'(_, _, _) -> error(overlay).

-spec 'vclock:prune_vclock1'(vclock:vclock(), integer(), vclock_props()) -> vclock:vclock().
'vclock:prune_vclock1'(_, _, _) -> error(overlay).

-spec 'vclock:prune_vclock1'(vclock:vclock(), integer(), vclock_props(), vclock:timestamp()) -> vclock:vclock().
'vclock:prune_vclock1'(_, _, _, _) -> error(overlay).

%% undefined for a missing key
-spec 'vclock:get_property'(atom(), vclock_props()) -> term().
'vclock:get_property'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_priority_queue
%% ---------------------------------------------------------------------------------------------

-type pq_entries() :: [{riak_core_priority_queue:priority(), riak_core_priority_queue:squeue()}].

-spec 'riak_core_priority_queue:merge'(pq_entries(), pq_entries(), pq_entries()) -> pq_entries().
'riak_core_priority_queue:merge'(_, _, _) -> error(overlay).

-spec 'riak_core_priority_queue:r2f'([any()]) -> riak_core_priority_queue:squeue().
'riak_core_priority_queue:r2f'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_base64url
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_base64url:urlencode'(string()) -> string(); (binary()) -> binary().
'riak_core_base64url:urlencode'(_) -> error(overlay).

-spec 'riak_core_base64url:urldecode'(string()) -> string(); (binary()) -> binary().
'riak_core_base64url:urldecode'(_) -> error(overlay).

-spec 'riak_core_base64url:padding'(binary()) -> binary(); (string()) -> string().
'riak_core_base64url:padding'(_) -> error(overlay).

-spec 'riak_core_base64url:urlencode_digit'(char()) -> char().
'riak_core_base64url:urlencode_digit'(_) -> error(overlay).

-spec 'riak_core_base64url:urldecode_digit'(char()) -> char().
'riak_core_base64url:urldecode_digit'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_rand
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_rand:uniform'() -> float().
'riak_core_rand:uniform'() -> error(overlay).

-spec 'riak_core_rand:uniform'(pos_integer()) -> pos_integer().
'riak_core_rand:uniform'(_) -> error(overlay).

%% the old random:uniform_s/2 took a seed of three integers
-spec 'riak_core_rand:uniform_s'(pos_integer(), {integer(), integer(), integer()} | rand:state()) -> {pos_integer(), rand:state()}.
'riak_core_rand:uniform_s'(_, _) -> error(overlay).

-spec 'riak_core_rand:seed'() -> rand:state().
'riak_core_rand:seed'() -> error(overlay).

-spec 'riak_core_rand:rand_bytes'(non_neg_integer()) -> binary().
'riak_core_rand:rand_bytes'(_) -> error(overlay).

-spec 'riak_core_rand:rand_seed'() -> erlang:timestamp().
'riak_core_rand:rand_seed'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_send_msg
%% ---------------------------------------------------------------------------------------------

%% the destination of erlang:send/3
-type send_dest() :: pid() | port() | atom() | {atom(), node()}.

%% the first argument is the From of a gen_server call
-spec 'riak_core_send_msg:reply_unreliable'({send_dest(), Tag}, Reply) -> {Tag, Reply}.
'riak_core_send_msg:reply_unreliable'(_, _) -> error(overlay).

-spec 'riak_core_send_msg:cast_unreliable'(send_dest(), Request) -> {'$gen_cast', Request}.
'riak_core_send_msg:cast_unreliable'(_, _) -> error(overlay).

%% {global, Name} and {via, Mod, Name} end in error({unimplemented_send, ..})
-spec 'riak_core_send_msg:send_event_unreliable'(send_dest() | {global, term()} | {via, module(), term()}, term()) -> ok.
'riak_core_send_msg:send_event_unreliable'(_, _) -> error(overlay).

-spec 'riak_core_send_msg:bang_unreliable'(send_dest(), Msg) -> Msg.
'riak_core_send_msg:bang_unreliable'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_bucket
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_bucket:append_bucket_defaults'(riak_core_bucket:properties()) -> ok.
'riak_core_bucket:append_bucket_defaults'(_) -> error(overlay).

%% the result is the one of set_bucket/2
-spec 'riak_core_bucket:set_bucket'(fun((riak_core_bucket:bucket(), riak_core_bucket:properties()) -> ok),
                                    riak_core_bucket:bucket(), riak_core_bucket:properties()) ->
          ok | {error, no_type | [{atom(), atom()}]}.
'riak_core_bucket:set_bucket'(_, _, _) -> error(overlay).

-spec 'riak_core_bucket:set_bucket_in_ring'(riak_core_bucket:bucket(), riak_core_bucket:properties()) -> ok.
'riak_core_bucket:set_bucket_in_ring'(_, _) -> error(overlay).

-spec 'riak_core_bucket:merge_props'(riak_core_bucket:properties(), riak_core_bucket:properties()) ->
          riak_core_bucket:properties().
'riak_core_bucket:merge_props'(_, _) -> error(overlay).

-spec 'riak_core_bucket:get_bucket'(riak_core_bucket:bucket()) -> riak_core_bucket:properties().
'riak_core_bucket:get_bucket'(_) -> error(overlay).

-spec 'riak_core_bucket:get_bucket'(riak_core_bucket:bucket(), riak_core_bucket:riak_core_ring()) ->
          riak_core_bucket:properties().
'riak_core_bucket:get_bucket'(_, _) -> error(overlay).

%% the second argument is the result of riak_core_ring_manager:get_bucket_meta/1
-spec 'riak_core_bucket:get_bucket_props'(riak_core_bucket:bucket(), undefined | {ok, riak_core_bucket:properties()}) ->
          riak_core_bucket:properties().
'riak_core_bucket:get_bucket_props'(_, _) -> error(overlay).

-spec 'riak_core_bucket:reset_bucket'(riak_core_bucket:bucket()) -> ok.
'riak_core_bucket:reset_bucket'(_) -> error(overlay).

%% the property name is the argument of get_bucket/1
-spec 'riak_core_bucket:name'(riak_core_bucket:properties()) -> riak_core_bucket:bucket().
'riak_core_bucket:name'(_) -> error(overlay).

-spec 'riak_core_bucket:n_val'(riak_core_bucket:properties()) -> pos_integer().
'riak_core_bucket:n_val'(_) -> error(overlay).

%% the key of the bucket in the meta data of the ring
-spec 'riak_core_bucket:bucket_key'(riak_core_bucket:bucket()) ->
          {bucket, binary()} | {riak_core_bucket:bucket_type(), binary()}.
'riak_core_bucket:bucket_key'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_bucket_props
%% ---------------------------------------------------------------------------------------------

%% the types that the spec of validate/4 spells out
-type bp_props() :: [{atom(), any()}].
-type bp_bucket() :: {riak_core_bucket:bucket_type(), undefined | binary()} | binary().
%% an error of the validation: the property and a message. validate/4 says {atom(), atom()}.
-type bp_error() :: {atom(), string()}.

%% the fifth argument is riak_core:bucket_validators(), the sixth the errors so far, a list per validator
-spec 'riak_core_bucket_props:validate'(create | update, bp_bucket(), undefined | bp_props(), bp_props(),
                                        [{atom(), module()}], [[bp_error()]]) ->
          {ok, bp_props()} | {error, [bp_error()]}.
'riak_core_bucket_props:validate'(_, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_bucket_props:validate_core_props'(create | update, bp_bucket(), undefined | bp_props(), bp_props()) ->
          [bp_error()].
'riak_core_bucket_props:validate_core_props'(_, _, _, _) -> error(overlay).

-spec 'riak_core_bucket_props:validate_core_prop'(create | update, bp_bucket(), undefined | bp_props(), {atom(), any()}) ->
          true | bp_error().
'riak_core_bucket_props:validate_core_prop'(_, _, _, _) -> error(overlay).

-spec 'riak_core_bucket_props:validate_reserved_names'(bp_bucket()) -> [{reserved_name, string()}].
'riak_core_bucket_props:validate_reserved_names'(_) -> error(overlay).

-spec 'riak_core_bucket_props:validate_reserved_name'(bp_bucket()) -> ok | string().
'riak_core_bucket_props:validate_reserved_name'(_) -> error(overlay).

%% two values of the same property, the result is one of them or their combination
-spec 'riak_core_bucket_props:resolve_prop'({atom(), any()}, {atom(), any()}) -> any().
'riak_core_bucket_props:resolve_prop'(_, _) -> error(overlay).

%% the values of precommit and postcommit
-spec 'riak_core_bucket_props:resolve_hooks'([term()], [term()]) -> [term()].
'riak_core_bucket_props:resolve_hooks'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_ring
%% ---------------------------------------------------------------------------------------------

%% Nodes: the module says node() for the members of the cluster (members field, claimant/1,
%% member_status/2, indices/2, pending_change()) and term() for the owner of a chstate, for the
%% owners in the chash and for the keys of the seen list (nodename and seen fields, owner_node/1,
%% all_owners/1, transfer_node/3, resize_transfer()). The specs below keep that split.

%% the members field of a chstate (without undefined): an orddict from the node to its status,
%% the vclock of the status and the meta data of the member
-type ring_member_info() :: {riak_core_ring:member_status(), vclock:vclock(), [{atom(), term()}]}.
-type ring_members() :: [{node(), ring_member_info()}].

%% the seen field of a chstate (without undefined): an orddict from the node to the vclock of
%% the last ring it has seen
-type ring_seen() :: [{term(), vclock:vclock()}].

%% an element of the next field of a chstate: index, owner, next owner (or '$resize', '$delete'),
%% the vnode modules that have finished their handoff, status
-type ring_next_entry() :: {chash:index_as_int(), term(), term(), [module()], awaiting | complete}.

%% a next entry of a ring that is being resized, the only kind that the reschedule functions take
-type ring_resize_entry() :: {chash:index_as_int(), term(), '$resize', [module()], awaiting | complete}.

%% the source or the target of a resize transfer; the specs of the module spell it {integer(), term()}
-type ring_idx_node() :: {chash:index_as_int(), term()}.

%% the record meta_entry (no field has a type): the value and the time of the last change in
%% gregorian seconds
-type ring_meta_entry() :: {meta_entry, term(), non_neg_integer()}.

-type ring_print_opt() :: numeric | legend | {out, io:device()} | {target_n, pos_integer()}.

-spec 'riak_core_ring:set_tainted'(riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:set_tainted'(_) -> error(overlay).

%% the message goes to logger:error/1 or to riak_core:stop/1, the callers give a string
-spec 'riak_core_ring:check_tainted'(riak_core_ring:chstate(), string()) -> ok.
'riak_core_ring:check_tainted'(_, _) -> error(overlay).

-spec 'riak_core_ring:set_chash'(riak_core_ring:chstate(), chash:chash()) -> riak_core_ring:chstate().
'riak_core_ring:set_chash'(_, _) -> error(overlay).

-spec 'riak_core_ring:members'(riak_core_ring:chstate(), [riak_core_ring:member_status()]) -> [node()].
'riak_core_ring:members'(_, _) -> error(overlay).

%% node() as in claiming_members/1 and down_members/1 (all_members/1 says term())
-spec 'riak_core_ring:active_members'(riak_core_ring:chstate()) -> [node()].
'riak_core_ring:active_members'(_) -> error(overlay).

-spec 'riak_core_ring:ready_members'(riak_core_ring:chstate()) -> [node()].
'riak_core_ring:ready_members'(_) -> error(overlay).

%% the last two arguments are num_partitions/1 and future_num_partitions/1 of the ring, both go to
%% chash:ring_increment/1; hence pos_integer() and not ring_size()
-spec 'riak_core_ring:future_index'(chash:index(), chash:index_as_int(), undefined | integer(),
                                    pos_integer(), pos_integer()) -> chash:index_as_int() | undefined.
'riak_core_ring:future_index'(_, _, _, _, _) -> error(overlay).

%% the first argument is the position of the source partition in the preflist of the key
-spec 'riak_core_ring:check_invalid_future_index'(integer(), pos_integer(), undefined | integer()) -> boolean().
'riak_core_ring:check_invalid_future_index'(_, _, _) -> error(overlay).

%% node() as the result of claimant/1 (the field says term())
-spec 'riak_core_ring:set_claimant'(riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:set_claimant'(_, _) -> error(overlay).

%% a name is {Node, Seed} (fresh/2, riak_core_claimant); undefined is not a name, only
%% reconcile_names/2 writes it
-spec 'riak_core_ring:set_cluster_name'(riak_core_ring:chstate(), {term(), term()}) -> riak_core_ring:chstate().
'riak_core_ring:set_cluster_name'(_, _) -> error(overlay).

-spec 'riak_core_ring:reconcile_names'(riak_core_ring:chstate(), riak_core_ring:chstate()) ->
          {riak_core_ring:chstate(), riak_core_ring:chstate()}.
'riak_core_ring:reconcile_names'(_, _) -> error(overlay).

-spec 'riak_core_ring:increment_vclock'(node(), riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:increment_vclock'(_, _) -> error(overlay).

-spec 'riak_core_ring:ring_version'(riak_core_ring:chstate()) -> vclock:vclock().
'riak_core_ring:ring_version'(_) -> error(overlay).

-spec 'riak_core_ring:increment_ring_version'(node(), riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:increment_ring_version'(_, _) -> error(overlay).

%% the value of the key, undefined for an unknown member or key
-spec 'riak_core_ring:get_member_meta'(riak_core_ring:chstate(), node(), atom()) -> term().
'riak_core_ring:get_member_meta'(_, _, _) -> error(overlay).

%% the first argument is the node that makes the change (it goes into the vclocks), the third the member
-spec 'riak_core_ring:update_member_meta'(node(), riak_core_ring:chstate(), node(), atom(), term()) ->
          riak_core_ring:chstate().
'riak_core_ring:update_member_meta'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_ring:update_member_meta'(node(), riak_core_ring:chstate(), node(), atom(), term(), same_vclock) ->
          riak_core_ring:chstate().
'riak_core_ring:update_member_meta'(_, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_ring:clear_member_meta'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:clear_member_meta'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:add_member'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:add_member'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:remove_member'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:remove_member'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:leave_member'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:leave_member'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:exit_member'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:exit_member'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:down_member'(node(), riak_core_ring:chstate(), node()) -> riak_core_ring:chstate().
'riak_core_ring:down_member'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:set_member'(node(), riak_core_ring:chstate(), node(), riak_core_ring:member_status()) ->
          riak_core_ring:chstate().
'riak_core_ring:set_member'(_, _, _, _) -> error(overlay).

-spec 'riak_core_ring:set_member'(node(), riak_core_ring:chstate(), node(), riak_core_ring:member_status(),
                                  same_vclock) -> riak_core_ring:chstate().
'riak_core_ring:set_member'(_, _, _, _, _) -> error(overlay).

%% the pairs are the arguments of transfer_node/3, e.g. the result of all_next_owners/1
-spec 'riak_core_ring:change_owners'(riak_core_ring:chstate(), [{chash:index_as_int(), term()}]) ->
          riak_core_ring:chstate().
'riak_core_ring:change_owners'(_, _) -> error(overlay).

-spec 'riak_core_ring:disowning_indices'(riak_core_ring:chstate(), node()) -> [chash:index_as_int()].
'riak_core_ring:disowning_indices'(_, _) -> error(overlay).

%% the owner comes from all_owners/1
-spec 'riak_core_ring:disowned_during_resize'(riak_core_ring:chstate(), chash:index_as_int(), term()) -> boolean().
'riak_core_ring:disowned_during_resize'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:pending_changes'(riak_core_ring:chstate()) -> [ring_next_entry()].
'riak_core_ring:pending_changes'(_) -> error(overlay).

-spec 'riak_core_ring:set_pending_changes'(riak_core_ring:chstate(), [ring_next_entry()]) ->
          riak_core_ring:chstate().
'riak_core_ring:set_pending_changes'(_, _) -> error(overlay).

%% node and new node are term() as in reschedule_resize_transfers/3; both clauses want a '$resize' entry
-spec 'riak_core_ring:reschedule_resize_operation'(term(), term(), ring_resize_entry(),
                                                   riak_core_ring:chstate()) ->
          {ring_resize_entry(), riak_core_ring:chstate()}.
'riak_core_ring:reschedule_resize_operation'(_, _, _, _) -> error(overlay).

%% the boolean says whether a transfer of the source was changed
-spec 'riak_core_ring:reschedule_inbound_resize_transfers'(ring_idx_node(), term(), term(),
                                                           riak_core_ring:chstate()) ->
          {boolean(), riak_core_ring:chstate()}.
'riak_core_ring:reschedule_inbound_resize_transfers'(_, _, _, _) -> error(overlay).

-spec 'riak_core_ring:reschedule_inbound_resize_transfer'(riak_core_ring:resize_transfer(), term(), term()) ->
          {riak_core_ring:resize_transfer(), boolean()}.
'riak_core_ring:reschedule_inbound_resize_transfer'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:reschedule_outbound_resize_transfers'(riak_core_ring:chstate(), chash:index_as_int(),
                                                            term(), term()) -> riak_core_ring:chstate().
'riak_core_ring:reschedule_outbound_resize_transfers'(_, _, _, _) -> error(overlay).

-spec 'riak_core_ring:clear_all_resize_transfers'(riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:clear_all_resize_transfers'(_) -> error(overlay).

%% the source first: the function is folded over all_owners/1
-spec 'riak_core_ring:clear_resize_transfers'(ring_idx_node(), riak_core_ring:chstate()) ->
          riak_core_ring:chstate().
'riak_core_ring:clear_resize_transfers'(_, _) -> error(overlay).

-spec 'riak_core_ring:cleanup_after_resize'(riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:cleanup_after_resize'(_) -> error(overlay).

%% the result is the one of vnode_type/2
-spec 'riak_core_ring:vnode_type'(riak_core_ring:chstate(), chash:index_as_int(), node()) ->
          primary | {fallback, term()} | future_primary | resized_primary.
'riak_core_ring:vnode_type'(_, _, _) -> error(overlay).

%% false is the result of lists:keyfind/3 on the next list
-spec 'riak_core_ring:next_owner_status'(false | ring_next_entry(), module()) -> riak_core_ring:pending_change().
'riak_core_ring:next_owner_status'(_, _) -> error(overlay).

%% the result of next_owner/2 for an entry that exists; never {undefined, undefined, undefined}
-spec 'riak_core_ring:next_owner'(ring_next_entry()) -> riak_core_ring:pending_change().
'riak_core_ring:next_owner'(_) -> error(overlay).

%% index, owner and next owner of the pending changes that are complete for the module
-spec 'riak_core_ring:completed_next_owners'(module(), riak_core_ring:chstate()) ->
          [{chash:index_as_int(), node(), node()}].
'riak_core_ring:completed_next_owners'(_, _) -> error(overlay).

-spec 'riak_core_ring:ring_ready'() -> boolean().
'riak_core_ring:ring_ready'() -> error(overlay).

%% the entries of the seen list of the members that have not seen the latest ring
-spec 'riak_core_ring:ring_ready_info'(riak_core_ring:chstate()) -> ring_seen().
'riak_core_ring:ring_ready_info'(_) -> error(overlay).

-spec 'riak_core_ring:ring_changed'(node(), riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:ring_changed'(_, _) -> error(overlay).

%% the second argument is is_resizing/1 of the ring
-spec 'riak_core_ring:future_ring'(riak_core_ring:chstate(), boolean()) -> riak_core_ring:chstate().
'riak_core_ring:future_ring'(_, _) -> error(overlay).

-spec 'riak_core_ring:pretty_print'(riak_core_ring:chstate(), [ring_print_opt()]) -> ok.
'riak_core_ring:pretty_print'(_, _) -> error(overlay).

-spec 'riak_core_ring:cancel_transfers'(riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:cancel_transfers'(_) -> error(overlay).

-spec 'riak_core_ring:internal_ring_changed'(node(), riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:internal_ring_changed'(_, _) -> error(overlay).

%% the pairs are the nodename and the meta field of the two rings
-spec 'riak_core_ring:merge_meta'({term(), dict:dict()}, {term(), dict:dict()}) -> dict:dict().
'riak_core_ring:merge_meta'(_, _) -> error(overlay).

-spec 'riak_core_ring:pick_val'({term(), ring_meta_entry()}, {term(), ring_meta_entry()}) -> ring_meta_entry().
'riak_core_ring:pick_val'(_, _) -> error(overlay).

-spec 'riak_core_ring:log_meta_merge'(dict:dict(), dict:dict(), dict:dict()) -> ok.
'riak_core_ring:log_meta_merge'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:log_ring_result'(riak_core_ring:chstate()) -> ok.
'riak_core_ring:log_ring_result'(_) -> error(overlay).

%% the boolean says whether the first ring was changed
-spec 'riak_core_ring:internal_reconcile'(riak_core_ring:chstate(), riak_core_ring:chstate()) ->
          {boolean(), riak_core_ring:chstate()}.
'riak_core_ring:internal_reconcile'(_, _) -> error(overlay).

%% the first argument is owner_node/1 of the first ring
-spec 'riak_core_ring:reconcile_divergent'(term(), riak_core_ring:chstate(), riak_core_ring:chstate()) ->
          riak_core_ring:chstate().
'riak_core_ring:reconcile_divergent'(_, _, _) -> error(overlay).

%% the merged members field; riak_core_gossip gives it to member_status/2
-spec 'riak_core_ring:reconcile_members'(riak_core_ring:chstate(), riak_core_ring:chstate()) -> ring_members().
'riak_core_ring:reconcile_members'(_, _) -> error(overlay).

-spec 'riak_core_ring:reconcile_seen'(riak_core_ring:chstate(), riak_core_ring:chstate()) -> ring_seen().
'riak_core_ring:reconcile_seen'(_, _) -> error(overlay).

-spec 'riak_core_ring:merge_next_status'(awaiting | complete, awaiting | complete) -> awaiting | complete.
'riak_core_ring:merge_next_status'(_, _) -> error(overlay).

-spec 'riak_core_ring:reconcile_next'([ring_next_entry()], [ring_next_entry()]) -> [ring_next_entry()].
'riak_core_ring:reconcile_next'(_, _) -> error(overlay).

-spec 'riak_core_ring:reconcile_divergent_next'([ring_next_entry()], [ring_next_entry()]) -> [ring_next_entry()].
'riak_core_ring:reconcile_divergent_next'(_, _) -> error(overlay).

%% written for any list of tuples with the key in the given position; the only use is with two
%% next lists and position 1
-spec 'riak_core_ring:substitute'(pos_integer(), [ring_next_entry()], [ring_next_entry()]) -> [ring_next_entry()].
'riak_core_ring:substitute'(_, _, _) -> error(overlay).

%% the third argument is get_members/1 of the merged members
-spec 'riak_core_ring:reconcile_ring'(riak_core_ring:chstate(), riak_core_ring:chstate(), [node()]) ->
          riak_core_ring:chstate().
'riak_core_ring:reconcile_ring'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:merge_status'(riak_core_ring:member_status(), riak_core_ring:member_status()) ->
          riak_core_ring:member_status().
'riak_core_ring:merge_status'(_, _) -> error(overlay).

%% module() as in handoff_complete/3 (deletion_complete/3 and resize_transfer_complete/4 say atom())
-spec 'riak_core_ring:transfer_complete'(riak_core_ring:chstate(), chash:index_as_int(), module()) ->
          riak_core_ring:chstate().
'riak_core_ring:transfer_complete'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:get_members'(ring_members()) -> [node()].
'riak_core_ring:get_members'(_) -> error(overlay).

-spec 'riak_core_ring:get_members'(ring_members(), [riak_core_ring:member_status()]) -> [node()].
'riak_core_ring:get_members'(_, _) -> error(overlay).

%% the node is a key of the seen list; ring_ready/1 and internal_reconcile/2 give owner_node/1
-spec 'riak_core_ring:update_seen'(term(), riak_core_ring:chstate()) -> riak_core_ring:chstate().
'riak_core_ring:update_seen'(_, _) -> error(overlay).

-spec 'riak_core_ring:equal_cstate'(riak_core_ring:chstate(), riak_core_ring:chstate()) -> boolean().
'riak_core_ring:equal_cstate'(_, _) -> error(overlay).

%% there is only the clause for false
-spec 'riak_core_ring:equal_cstate'(riak_core_ring:chstate(), riak_core_ring:chstate(), false) -> boolean().
'riak_core_ring:equal_cstate'(_, _, _) -> error(overlay).

-spec 'riak_core_ring:equal_members'(ring_members(), ring_members()) -> boolean().
'riak_core_ring:equal_members'(_, _) -> error(overlay).

-spec 'riak_core_ring:equal_seen'(riak_core_ring:chstate(), riak_core_ring:chstate()) -> boolean().
'riak_core_ring:equal_seen'(_, _) -> error(overlay).

%% the seen list without the nodes that are no members
-spec 'riak_core_ring:filtered_seen'(riak_core_ring:chstate()) -> ring_seen().
'riak_core_ring:filtered_seen'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_util
%% ---------------------------------------------------------------------------------------------

%% the riak_object:bkey() of the @spec comments: a bucket and a key
-type util_bkey() :: {riak_core_bucket:bucket(), binary()}.

%% the records riak_core_fold_req_v1 and riak_core_fold_req_v2 of riak_core_vnode.hrl
-type util_fold_req_v1() :: {riak_core_fold_req_v1, fun(), term()}.
-type util_fold_req_v2() :: {riak_core_fold_req_v2, fun(), term(), boolean(), list()}.
%% make_fold_reqv/5 wants a fun of arity 3: key, value and accumulator to the new accumulator
-type util_fold_fun() :: fun((term(), term(), term()) -> term()).

%% the record pmap_acc; no field has a type, these are the values that pmap/3 keeps in them.
%% done and the results of the workers are pairs of the position in the input and the value.
-type util_pmap_result() :: {non_neg_integer(), term()}.
-type util_pmap_acc() :: {pmap_acc, pid(), fun((term()) -> term()), non_neg_integer(), sets:set(pid()),
                          non_neg_integer(), [util_pmap_result()], pos_integer()}.

%% inet:ip_address() and inet:port_number(); riak_core_util does not mention inet
-type util_ip_address() :: {0..255, 0..255, 0..255, 0..255} |
                           {0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535}.
-type util_port_number() :: 0..65535.

%% the reason of a failed file operation: a posix error, or any other term, which is printed as it is
%% (file:list_dir/1 has {no_translation, Filename}). erl_posix_msg:message/1 says atom().
-spec 'riak_core_util:posix_error'(term()) -> string().
'riak_core_util:posix_error'(_) -> error(overlay).

-spec 'riak_core_util:moment'() -> integer().
'riak_core_util:moment'() -> error(overlay).

%% the @spec says two strings, the @doc and the code also take now() tuples
-spec 'riak_core_util:compare_dates'(string() | erlang:timestamp(), string() | erlang:timestamp()) -> boolean().
'riak_core_util:compare_dates'(_, _) -> error(overlay).

-spec 'riak_core_util:rfc1123_to_now'(string()) -> erlang:timestamp().
'riak_core_util:rfc1123_to_now'(_) -> error(overlay).

-spec 'riak_core_util:make_tmp_dir'() -> string().
'riak_core_util:make_tmp_dir'() -> error(overlay).

%% the file name comes from replace_file/2
-spec 'riak_core_util:read_file'(string()) -> {ok, binary()}.
'riak_core_util:read_file'(_) -> error(overlay).

-spec 'riak_core_util:read_file'(file:io_device(), [binary()]) -> [binary()].
'riak_core_util:read_file'(_, _) -> error(overlay).

%% the types of the @spec; a base outside of 2..62 is a badarg
-spec 'riak_core_util:integer_to_list'(integer(), integer()) -> string().
'riak_core_util:integer_to_list'(_, _) -> error(overlay).

-spec 'riak_core_util:integer_to_list'(integer(), integer(), string()) -> string().
'riak_core_util:integer_to_list'(_, _, _) -> error(overlay).

-spec 'riak_core_util:sha'(binary()) -> binary().
'riak_core_util:sha'(_) -> error(overlay).

-spec 'riak_core_util:md5'(binary()) -> binary().
'riak_core_util:md5'(_) -> error(overlay).

%% the @spec says list(), the code builds a binary of 32 bits
-spec 'riak_core_util:mkclientid'(term()) -> <<_:32>>.
'riak_core_util:mkclientid'(_) -> error(overlay).

-spec 'riak_core_util:chash_key'(util_bkey()) -> chash:index().
'riak_core_util:chash_key'(_) -> error(overlay).

%% the bucket properties as the @spec spells them
-spec 'riak_core_util:chash_key'(util_bkey(), [{atom(), any()}]) -> chash:index().
'riak_core_util:chash_key'(_, _) -> error(overlay).

-spec 'riak_core_util:chash_std_keyfun'(util_bkey()) -> chash:index().
'riak_core_util:chash_std_keyfun'(_) -> error(overlay).

-spec 'riak_core_util:chash_bucketonly_keyfun'(util_bkey()) -> chash:index().
'riak_core_util:chash_bucketonly_keyfun'(_) -> error(overlay).

-spec 'riak_core_util:str_to_node'(atom() | string()) -> node().
'riak_core_util:str_to_node'(_) -> error(overlay).

%% [] if the local node has no host name
-spec 'riak_core_util:node_hostname'() -> string().
'riak_core_util:node_hostname'() -> error(overlay).

-spec 'riak_core_util:start_app_deps'(atom()) -> ok.
'riak_core_util:start_app_deps'(_) -> error(overlay).

-spec 'riak_core_util:ensure_started'(atom()) -> ok.
'riak_core_util:ensure_started'(_) -> error(overlay).

%% the fold fun of pmap/3 over the input list
-spec 'riak_core_util:pmap_worker'(term(), util_pmap_acc()) -> util_pmap_acc().
'riak_core_util:pmap_worker'(_, _) -> error(overlay).

-spec 'riak_core_util:pmap_collect_one'(sets:set(pid())) -> {util_pmap_result(), sets:set(pid())}.
'riak_core_util:pmap_collect_one'(_) -> error(overlay).

-spec 'riak_core_util:pmap_collect_rest'(sets:set(pid()), [util_pmap_result()]) -> [util_pmap_result()].
'riak_core_util:pmap_collect_rest'(_, _) -> error(overlay).

%% the result of rpc:multicall/5
-spec 'riak_core_util:rpc_every_member'(module(), atom(), [term()], timeout()) -> {[term()], [node()]}.
'riak_core_util:rpc_every_member'(_, _, _, _) -> error(overlay).

%% the result of multicall_ann/5
-spec 'riak_core_util:rpc_every_member_ann'(module(), atom(), [term()], timeout()) ->
          {[{node(), term()}], [node()]}.
'riak_core_util:rpc_every_member_ann'(_, _, _, _) -> error(overlay).

%% the keys with different values and both values; '$none' stands for a missing key
-spec 'riak_core_util:orddict_delta'(orddict:orddict(Key, A), orddict:orddict(Key, B)) ->
          orddict:orddict(Key, {A | '$none', B | '$none'}).
'riak_core_util:orddict_delta'(_, _) -> error(overlay).

-spec 'riak_core_util:shuffle'([T]) -> [T].
'riak_core_util:shuffle'(_) -> error(overlay).

-spec 'riak_core_util:format_ip_and_port'(string() | util_ip_address(), util_port_number()) -> string().
'riak_core_util:format_ip_and_port'(_, _) -> error(overlay).

%% the socket is whatever the transport module (gen_tcp, ssl, a ranch transport) works on
-spec 'riak_core_util:peername'(term(), module()) -> string().
'riak_core_util:peername'(_, _) -> error(overlay).

-spec 'riak_core_util:sockname'(term(), module()) -> string().
'riak_core_util:sockname'(_, _) -> error(overlay).

-spec 'riak_core_util:make_fold_req'(util_fold_req_v1() | util_fold_req_v2()) -> util_fold_req_v2().
'riak_core_util:make_fold_req'(_) -> error(overlay).

-spec 'riak_core_util:make_fold_req'(util_fold_fun(), term()) -> util_fold_req_v2().
'riak_core_util:make_fold_req'(_, _) -> error(overlay).

-spec 'riak_core_util:make_fold_req'(util_fold_fun(), term(), boolean(), list()) -> util_fold_req_v2().
'riak_core_util:make_fold_req'(_, _, _, _) -> error(overlay).

-spec 'riak_core_util:make_newest_fold_req'(util_fold_req_v1() | util_fold_req_v2()) -> util_fold_req_v2().
'riak_core_util:make_newest_fold_req'(_) -> error(overlay).

%% {error, Reason} if the proxy process dies before it answers
-spec 'riak_core_util:proxy_spawn'(fun(() -> Result)) -> Result | {error, term()}.
'riak_core_util:proxy_spawn'(_) -> error(overlay).

%% the first argument is the version of the record; it is ignored, the callers pass v2
-spec 'riak_core_util:make_fold_reqv'(v1 | v2, util_fold_fun(), term(), boolean(), list()) -> util_fold_req_v2().
'riak_core_util:make_fold_reqv'(_, _, _, _, _) -> error(overlay).

%% the body of the proxy process: the message sent to the parent, or ok if the parent is gone
-spec 'riak_core_util:proxy'(pid(), fun(() -> Result)) -> ok | {proxy_reply, reference(), Result}.
'riak_core_util:proxy'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_apl
%% ---------------------------------------------------------------------------------------------

%% docidx() as in get_apl/3; get_apl_ann/4 says binary()
-spec 'riak_core_apl:get_apl_ann'(riak_core_apl:docidx(), riak_core_apl:n_val(), [node()]) ->
          riak_core_apl:preflist_ann().
'riak_core_apl:get_apl_ann'(_, _, _) -> error(overlay).

%% the second argument is a service of the node watcher, as in get_apl/3
-spec 'riak_core_apl:first_up'(riak_core_apl:docidx(), atom()) -> {riak_core_apl:index(), node()}.
'riak_core_apl:first_up'(_, _) -> error(overlay).

-spec 'riak_core_apl:offline_owners'(atom()) -> riak_core_apl:preflist().
'riak_core_apl:offline_owners'(_) -> error(overlay).

%% a service or the ordset of the nodes that are up. chashbin:chashbin() as in get_apl_chbin/4;
%% the type chashbin() of riak_core_apl is term().
-spec 'riak_core_apl:offline_owners'(atom() | [node()], chashbin:chashbin()) -> riak_core_apl:preflist().
'riak_core_apl:offline_owners'(_, _) -> error(overlay).

-spec 'riak_core_apl:is_up'(node(), [node()]) -> boolean().
'riak_core_apl:is_up'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_ring_util
%% ---------------------------------------------------------------------------------------------

%% a preflist of riak_core_ring:all_preflists/2, which says Node :: term() for the owner
-type ring_util_preflist() :: [{chash:index_as_int(), node()}].

-spec 'riak_core_ring_util:assign'(chash:index_as_int(), node()) -> ok.
'riak_core_ring_util:assign'(_, _) -> error(overlay).

%% the ordset of the preflists that have less distinct nodes than n_val
-spec 'riak_core_ring_util:check_ring'() -> [ring_util_preflist()].
'riak_core_ring_util:check_ring'() -> error(overlay).

-spec 'riak_core_ring_util:check_ring'(riak_core_ring:riak_core_ring()) -> [ring_util_preflist()].
'riak_core_ring_util:check_ring'(_) -> error(overlay).

-spec 'riak_core_ring_util:check_ring'(riak_core_ring:riak_core_ring(), pos_integer()) -> [ring_util_preflist()].
'riak_core_ring_util:check_ring'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_status
%% ---------------------------------------------------------------------------------------------

%% the rings of the reachable nodes, an orddict by the node that owns the ring
-type status_rings() :: [{node(), riak_core_ring:riak_core_ring()}].
%% partitions as in the spec of active_partitions/1
-type status_partitions() :: ordsets:ordset(non_neg_integer()).
%% a pending transfer: index, the vnode modules still waiting (down if the owner is not reachable),
%% the modules that are done, the status
-type status_transfer() :: {non_neg_integer(), down | [module()], [module()], awaiting | complete}.

%% claimant, ring ready (undefined if the claimant is not reachable), unreachable nodes, nodes marked
%% down, the pending transfers by {Owner, NextOwner}
-spec 'riak_core_status:ring_status'() ->
          {node(), boolean() | undefined, [node()], [node()], [{{node(), node()}, [status_transfer()]}]}.
'riak_core_status:ring_status'() -> error(overlay).

%% the sorted nodes that are down, and the rings
-spec 'riak_core_status:get_rings'() -> {[node()], status_rings()}.
'riak_core_status:get_rings'() -> error(overlay).

-spec 'riak_core_status:hash_ring'(riak_core_ring:riak_core_ring()) -> non_neg_integer().
'riak_core_status:hash_ring'(_) -> error(overlay).

%% the first argument is a result of hash_ring/1
-spec 'riak_core_status:rings_match'(non_neg_integer(), status_rings()) -> true | {false, node()}.
'riak_core_status:rings_match'(_, _) -> error(overlay).

%% primary, secondary and stopped partitions of the node
-spec 'riak_core_status:partitions'(node(), riak_core_ring:riak_core_ring()) ->
          {status_partitions(), status_partitions(), status_partitions()}.
'riak_core_status:partitions'(_, _) -> error(overlay).

%% the first argument is the result of riak_core_ring:all_owners/1
-spec 'riak_core_status:owned_partitions'([{non_neg_integer(), node()}], node()) -> [non_neg_integer()].
'riak_core_status:owned_partitions'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% gen_fsm_compat
%% ---------------------------------------------------------------------------------------------

%% The types of OTP's gen_fsm (fsm_name(), fsm_ref(), start_opt(), enter_loop_opt(), from()).
%% the name to register: gen:emgr_name()
-type fsm_name() :: {local, atom()} | {global, term()} | {via, module(), term()}.
%% what gen:call/3,4 and gen:stop/1,3 accept
-type fsm_ref() :: pid() | atom() | {atom(), node()} | {global, term()} | {via, module(), term()}.
%% gen:option(); hibernate_after as in gen_server, the code reads it in init_it/6 and enter_loop/6
-type fsm_enter_loop_opt() :: {hibernate_after, timeout()} | {debug, [sys:debug_option()]}.
-type fsm_start_opt() :: {timeout, timeout()} | {spawn_opt, [proc_lib:start_spawn_option()]} |
                         fsm_enter_loop_opt().
%% gen:start_ret() without the result of a start with monitor
-type fsm_start_ret() :: {ok, pid()} | ignore | {error, term()}.
%% the client of a sync event
-type fsm_from() :: {pid(), term()}.

%% The arguments of the loop.
%% the name of the process, a result of gen:name/1 or gen:get_proc_name/1: the pid, the local name
%% or the term registered with global or with a via module
-type fsm_proc_name() :: term().
%% hibernate if the callback asked for it
-type fsm_time() :: timeout() | hibernate.
-type fsm_debug() :: [sys:dbg_opt()].
%% Misc of the sys callbacks: [Name, StateName, StateData, Mod, Time, HibernateAfterTimeout];
%% written as in the spec of system_terminate/4
-type fsm_misc() :: [term(), ...].
%% what the callbacks of the behaviour may return (the -callback declarations and the state functions)
-type fsm_result() :: {next_state, atom(), term()} | {next_state, atom(), term(), fsm_time()} |
                      {reply, term(), atom(), term()} | {reply, term(), atom(), term(), fsm_time()} |
                      {stop, term(), term()} | {stop, term(), term(), term()}.

-spec 'gen_fsm_compat:start'(module(), term(), [fsm_start_opt()]) -> fsm_start_ret().
'gen_fsm_compat:start'(_, _, _) -> error(overlay).

-spec 'gen_fsm_compat:start'(fsm_name(), module(), term(), [fsm_start_opt()]) -> fsm_start_ret().
'gen_fsm_compat:start'(_, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:start_link'(module(), term(), [fsm_start_opt()]) -> fsm_start_ret().
'gen_fsm_compat:start_link'(_, _, _) -> error(overlay).

-spec 'gen_fsm_compat:start_link'(fsm_name(), module(), term(), [fsm_start_opt()]) -> fsm_start_ret().
'gen_fsm_compat:start_link'(_, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:stop'(fsm_ref()) -> ok.
'gen_fsm_compat:stop'(_) -> error(overlay).

-spec 'gen_fsm_compat:stop'(fsm_ref(), term(), timeout()) -> ok.
'gen_fsm_compat:stop'(_, _, _) -> error(overlay).

-spec 'gen_fsm_compat:send_event'(fsm_ref(), term()) -> ok.
'gen_fsm_compat:send_event'(_, _) -> error(overlay).

%% the result is the reply of the fsm
-spec 'gen_fsm_compat:sync_send_event'(fsm_ref(), term()) -> term().
'gen_fsm_compat:sync_send_event'(_, _) -> error(overlay).

-spec 'gen_fsm_compat:sync_send_event'(fsm_ref(), term(), timeout()) -> term().
'gen_fsm_compat:sync_send_event'(_, _, _) -> error(overlay).

-spec 'gen_fsm_compat:send_all_state_event'(fsm_ref(), term()) -> ok.
'gen_fsm_compat:send_all_state_event'(_, _) -> error(overlay).

-spec 'gen_fsm_compat:sync_send_all_state_event'(fsm_ref(), term()) -> term().
'gen_fsm_compat:sync_send_all_state_event'(_, _) -> error(overlay).

-spec 'gen_fsm_compat:sync_send_all_state_event'(fsm_ref(), term(), timeout()) -> term().
'gen_fsm_compat:sync_send_all_state_event'(_, _, _) -> error(overlay).

-spec 'gen_fsm_compat:start_timer'(non_neg_integer(), term()) -> reference().
'gen_fsm_compat:start_timer'(_, _) -> error(overlay).

-spec 'gen_fsm_compat:send_event_after'(non_neg_integer(), term()) -> reference().
'gen_fsm_compat:send_event_after'(_, _) -> error(overlay).

%% the remaining time, false if the timer was not active
-spec 'gen_fsm_compat:cancel_timer'(reference()) -> non_neg_integer() | false.
'gen_fsm_compat:cancel_timer'(_) -> error(overlay).

-spec 'gen_fsm_compat:enter_loop'(module(), [fsm_enter_loop_opt()], atom(), term()) -> no_return().
'gen_fsm_compat:enter_loop'(_, _, _, _) -> error(overlay).

%% the fifth argument is the registered name or the timeout
-spec 'gen_fsm_compat:enter_loop'(module(), [fsm_enter_loop_opt()], atom(), term(), fsm_name() | timeout()) ->
          no_return().
'gen_fsm_compat:enter_loop'(_, _, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:enter_loop'(module(), [fsm_enter_loop_opt()], atom(), term(), fsm_name() | pid(),
                                  timeout()) -> no_return().
'gen_fsm_compat:enter_loop'(_, _, _, _, _, _) -> error(overlay).

%% called by gen:init_it/6,7: starter, parent (self for a start without link), the name or the pid,
%% the callback module, its arguments, the options
-spec 'gen_fsm_compat:init_it'(pid(), self | pid(), fsm_name() | pid(), module(), term(), [fsm_start_opt()]) ->
          no_return().
'gen_fsm_compat:init_it'(_, _, _, _, _, _) -> error(overlay).

%% parent, name, state name, state data, callback module, timeout, hibernate_after, debug
-spec 'gen_fsm_compat:loop'(pid(), fsm_proc_name(), atom(), term(), module(), fsm_time(), timeout(),
                            fsm_debug()) -> no_return().
'gen_fsm_compat:loop'(_, _, _, _, _, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:wake_hib'(pid(), fsm_proc_name(), atom(), term(), module(), timeout(), fsm_debug()) ->
          no_return().
'gen_fsm_compat:wake_hib'(_, _, _, _, _, _, _) -> error(overlay).

%% the first argument is any message of the mailbox, the last says if the process was hibernating
-spec 'gen_fsm_compat:decode_msg'(term(), pid(), fsm_proc_name(), atom(), term(), module(), fsm_time(),
                                  timeout(), fsm_debug(), boolean()) -> no_return().
'gen_fsm_compat:decode_msg'(_, _, _, _, _, _, _, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:system_continue'(pid(), fsm_debug(), fsm_misc()) -> no_return().
'gen_fsm_compat:system_continue'(_, _, _) -> error(overlay).

%% {ok, NewMisc}; any other result of Mod:code_change/4 and its 'EXIT' are handed on to sys
-spec 'gen_fsm_compat:system_code_change'(fsm_misc(), module(), term(), term()) -> {ok, fsm_misc()} | term().
'gen_fsm_compat:system_code_change'(_, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:system_get_state'(fsm_misc()) -> {ok, {atom(), term()}}.
'gen_fsm_compat:system_get_state'(_) -> error(overlay).

%% the fun maps state name and state data to the new ones
-spec 'gen_fsm_compat:system_replace_state'(fun(({atom(), term()}) -> {atom(), term()}), fsm_misc()) ->
          {ok, {atom(), term()}, fsm_misc()}.
'gen_fsm_compat:system_replace_state'(_, _) -> error(overlay).

%% the format fun for sys:handle_debug/4. Two functions in one: for in and return the third argument is
%% {Name, StateName}, for out it is Name, and the callers give it accordingly
-spec 'gen_fsm_compat:print_event'(io:device(), {in, term()} | return, {fsm_proc_name(), atom()}) -> ok;
                                  (io:device(), {out, term(), pid(), atom()}, fsm_proc_name()) -> ok.
'gen_fsm_compat:print_event'(_, _, _) -> error(overlay).

%% without debug options
-spec 'gen_fsm_compat:handle_msg'(term(), pid(), fsm_proc_name(), atom(), term(), module(), fsm_time(),
                                  timeout()) -> no_return().
'gen_fsm_compat:handle_msg'(_, _, _, _, _, _, _, _) -> error(overlay).

-spec 'gen_fsm_compat:handle_msg'(term(), pid(), fsm_proc_name(), atom(), term(), module(), fsm_time(),
                                  timeout(), fsm_debug()) -> no_return().
'gen_fsm_compat:handle_msg'(_, _, _, _, _, _, _, _, _) -> error(overlay).

%% the result of the callback that the message goes to
-spec 'gen_fsm_compat:dispatch'(term(), module(), atom(), term()) -> fsm_result().
'gen_fsm_compat:dispatch'(_, _, _, _) -> error(overlay).

%% the client if the message is a sync event
-spec 'gen_fsm_compat:from'(term()) -> fsm_from() | undefined.
'gen_fsm_compat:from'(_) -> error(overlay).

%% the result of the send under a catch; OTP's gen_fsm says term()
-spec 'gen_fsm_compat:reply'(fsm_from(), term()) -> term().
'gen_fsm_compat:reply'(_, _) -> error(overlay).

-spec 'gen_fsm_compat:reply'(fsm_proc_name(), fsm_from(), term(), fsm_debug(), atom()) -> fsm_debug().
'gen_fsm_compat:reply'(_, _, _, _, _) -> error(overlay).

%% reason, name, last message, state name, the formatted state data, debug
-spec 'gen_fsm_compat:error_info'(term(), fsm_proc_name(), term(), atom(), term(), fsm_debug()) -> ok.
'gen_fsm_compat:error_info'(_, _, _, _, _, _) -> error(overlay).

%% a format string for the last message
-spec 'gen_fsm_compat:get_msg_str'(term()) -> string().
'gen_fsm_compat:get_msg_str'(_) -> error(overlay).

-spec 'gen_fsm_compat:get_msg'(term()) -> term().
'gen_fsm_compat:get_msg'(_) -> error(overlay).

%% called by sys with [PDict, SysState, Parent, Debug, Misc]; the result starts with a header and a
%% data tuple, the rest is the status of the callback module
-spec 'gen_fsm_compat:format_status'(normal | terminate, [term(), ...]) -> [term(), ...].
'gen_fsm_compat:format_status'(_, _) -> error(overlay).

%% the status that Mod:format_status/2 makes of the process dictionary and the state data
-spec 'gen_fsm_compat:format_status'(normal | terminate, module(), [{term(), term()}], term()) -> term().
'gen_fsm_compat:format_status'(_, _, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_claim
%% ---------------------------------------------------------------------------------------------

%% Nodes are node() as in the specs of the module (get_deltas/4, get_counts/2, sequential_claim/3),
%% although riak_core_ring:all_owners/1 and all_members/1 say term(). The ring size and the number
%% of nodes are pos_integer() as in get_deltas/4.

%% a partition index, i.e. chash:index_as_int(); the module does not mention chash
-type claim_index() :: integer().

%% the result of riak_core_ring:all_owners/1
-type claim_owners() :: [{claim_index(), node()}].

%% a partition as the choose function sees it: its position in the ring (0 .. RingSize - 1) and
%% its index
-type claim_nth() :: {non_neg_integer(), claim_index()}.

%% the number of partitions per node: what it owns, or what it should own (wants/1)
-type claim_counts() :: [{node(), non_neg_integer()}].

%% per node the number of partitions it should gain (positive) or may lose (negative), the Deltas
%% of get_deltas/4
-type claim_deltas() :: [{node(), integer()}].

%% the parameters of a choose function, a proplist; only target_n_val is read
-type claim_params() :: [{target_n_val, pos_integer()} | {atom(), term()}].

-spec 'riak_core_claim:claim'(riak_core_ring:riak_core_ring()) -> riak_core_ring:riak_core_ring().
'riak_core_claim:claim'(_) -> error(overlay).

%% the second and the third argument are ignored. claim/1 passes the atoms want and choose, riak_core
%% had the {Module, Function} of the wants function and of the choose function there.
-spec 'riak_core_claim:claim'(riak_core_ring:riak_core_ring(), term(), term()) -> riak_core_ring:riak_core_ring().
'riak_core_claim:claim'(_, _, _) -> error(overlay).

-spec 'riak_core_claim:claim_until_balanced'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:claim_until_balanced'(_, _) -> error(overlay).

%% here the two atoms are matched
-spec 'riak_core_claim:claim_until_balanced'(riak_core_ring:riak_core_ring(), node(), want, choose) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:claim_until_balanced'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claim:default_choose_claim'(riak_core_ring:riak_core_ring()) -> riak_core_ring:riak_core_ring().
'riak_core_claim:default_choose_claim'(_) -> error(overlay).

-spec 'riak_core_claim:default_choose_claim'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:default_choose_claim'(_, _) -> error(overlay).

-spec 'riak_core_claim:default_choose_claim'(riak_core_ring:riak_core_ring(), node(), claim_params()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:default_choose_claim'(_, _, _) -> error(overlay).

%% the result as the @spec comment gives it; the number is the count of partitions that the node
%% still wants and is always positive
-spec 'riak_core_claim:default_wants_claim'(riak_core_ring:riak_core_ring()) -> {yes, integer()} | no.
'riak_core_claim:default_wants_claim'(_) -> error(overlay).

-spec 'riak_core_claim:default_wants_claim'(riak_core_ring:riak_core_ring(), node()) -> {yes, integer()} | no.
'riak_core_claim:default_wants_claim'(_, _) -> error(overlay).

-spec 'riak_core_claim:wants_claim_v2'(riak_core_ring:riak_core_ring()) -> {yes, integer()} | no.
'riak_core_claim:wants_claim_v2'(_) -> error(overlay).

-spec 'riak_core_claim:wants_claim_v2'(riak_core_ring:riak_core_ring(), node()) -> {yes, integer()} | no.
'riak_core_claim:wants_claim_v2'(_, _) -> error(overlay).

-spec 'riak_core_claim:default_choose_params'() -> claim_params().
'riak_core_claim:default_choose_params'() -> error(overlay).

-spec 'riak_core_claim:default_choose_params'(claim_params()) -> claim_params().
'riak_core_claim:default_choose_params'(_) -> error(overlay).

-spec 'riak_core_claim:choose_claim_v2'(riak_core_ring:riak_core_ring()) -> riak_core_ring:riak_core_ring().
'riak_core_claim:choose_claim_v2'(_) -> error(overlay).

-spec 'riak_core_claim:choose_claim_v2'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:choose_claim_v2'(_, _) -> error(overlay).

-spec 'riak_core_claim:choose_claim_v2'(riak_core_ring:riak_core_ring(), node(), claim_params()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:choose_claim_v2'(_, _, _) -> error(overlay).

%% false: two partitions of a node are closer than target_n. {true, Indices}: no such pair, except
%% for the partitions Indices, which are too close to the first partition of their node across the
%% end of the ring.
-spec 'riak_core_claim:meets_target_n'(riak_core_ring:riak_core_ring(), pos_integer()) ->
          {true, [claim_index()]} | false.
'riak_core_claim:meets_target_n'(_, _) -> error(overlay).

%% the position of the next owner, then per node its first position and its last position with
%% the index of that partition
-spec 'riak_core_claim:meets_target_n'(claim_owners(), pos_integer(), non_neg_integer(),
                                       [{node(), non_neg_integer()}],
                                       [{node(), non_neg_integer(), claim_index()}]) ->
          {true, [claim_index()]} | false.
'riak_core_claim:meets_target_n'(_, _, _, _, _) -> error(overlay).

%% Wants is the result of wants/1. Owners is the list of the current owners in ring order, only its
%% length is used; the result has the new owners in the same form.
-spec 'riak_core_claim:claim_diversify'(claim_counts(), [node()], claim_params()) -> {[node()], [diversified]}.
'riak_core_claim:claim_diversify'(_, _, _) -> error(overlay).

-spec 'riak_core_claim:claim_diagonal'(claim_counts(), [node()], claim_params()) -> {[node()], [diagonalized]}.
'riak_core_claim:claim_diagonal'(_, _, _) -> error(overlay).

-spec 'riak_core_claim:claim_rebalance_n'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:claim_rebalance_n'(_, _) -> error(overlay).

%% choose_claim_v2/3 pads the nodes with the atom undefined, which is a node() as well
-spec 'riak_core_claim:diagonal_stripe'(riak_core_ring:riak_core_ring(), [node()]) -> claim_owners().
'riak_core_claim:diagonal_stripe'(_, _) -> error(overlay).

-spec 'riak_core_claim:random_choose_claim'(riak_core_ring:riak_core_ring()) -> riak_core_ring:riak_core_ring().
'riak_core_claim:random_choose_claim'(_) -> error(overlay).

-spec 'riak_core_claim:random_choose_claim'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:random_choose_claim'(_, _) -> error(overlay).

%% the parameters are ignored, the signature is the one of a choose function
-spec 'riak_core_claim:random_choose_claim'(riak_core_ring:riak_core_ring(), node(), claim_params()) ->
          riak_core_ring:riak_core_ring().
'riak_core_claim:random_choose_claim'(_, _, _) -> error(overlay).

%% the arguments are ignored, the signatures are the ones of a wants function (see the @spec comment)
-spec 'riak_core_claim:never_wants_claim'(riak_core_ring:riak_core_ring()) -> no.
'riak_core_claim:never_wants_claim'(_) -> error(overlay).

-spec 'riak_core_claim:never_wants_claim'(riak_core_ring:riak_core_ring(), node()) -> no.
'riak_core_claim:never_wants_claim'(_, _) -> error(overlay).

%% a violation is the list [PrevIdx, Idx] of two partitions of one node that are closer than target_n
-spec 'riak_core_claim:find_violations'(riak_core_ring:riak_core_ring(), pos_integer()) -> [[claim_index()]].
'riak_core_claim:find_violations'(_, _) -> error(overlay).

%% the third argument is the delta of an owner that has none yet
-spec 'riak_core_claim:add_default_deltas'(claim_owners(), claim_deltas(), integer()) -> claim_deltas().
'riak_core_claim:add_default_deltas'(_, _, _) -> error(overlay).

%% all partitions, the candidates, target_n, ring size; the result is the rest of the candidates
-spec 'riak_core_claim:prefilter_violations'(riak_core_ring:riak_core_ring(), node(), [claim_nth()],
                                             [claim_nth()], pos_integer(), pos_integer()) -> [claim_nth()].
'riak_core_claim:prefilter_violations'(_, _, _, _, _, _) -> error(overlay).

%% the candidates, target_n, ring size; the result has the indices to claim
-spec 'riak_core_claim:select_indices'(claim_owners(), claim_deltas(), [claim_nth()], pos_integer(),
                                       pos_integer()) -> [claim_index()].
'riak_core_claim:select_indices'(_, _, _, _, _) -> error(overlay).

%% two positions in the ring, target_n, ring size
-spec 'riak_core_claim:spaced_by_n'(non_neg_integer(), non_neg_integer(), pos_integer(), pos_integer()) ->
          boolean().
'riak_core_claim:spaced_by_n'(_, _, _, _) -> error(overlay).

%% what the nodes should own and what they own
-spec 'riak_core_claim:wants_owns_diff'(claim_counts(), claim_counts()) -> claim_deltas().
'riak_core_claim:wants_owns_diff'(_, _) -> error(overlay).

-spec 'riak_core_claim:wants'(riak_core_ring:riak_core_ring()) -> claim_counts().
'riak_core_claim:wants'(_) -> error(overlay).

%% the number of claiming nodes and the ring size
-spec 'riak_core_claim:wants_counts'(pos_integer(), pos_integer()) -> [non_neg_integer()].
'riak_core_claim:wants_counts'(_, _) -> error(overlay).

%% a float as for ceiling/1; the guard asks for a number that is not negative
-spec 'riak_core_claim:roundup'(float()) -> non_neg_integer().
'riak_core_claim:roundup'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_claim_util
%% ---------------------------------------------------------------------------------------------

%% The module has no spec and no type. Its lists hold node names (the comments say so, and
%% riak_core_claim passes nodes), so the specs say node() where the code would take any term.

%% an ownership list: the owner of each partition in ring order
-type cu_owners() :: [node()].

%% a distance in an ownership list: the number of partitions between a partition and a following
%% partition of another node
-type cu_dist() :: non_neg_integer().

-type cu_pair() :: {node(), node()}.

%% adjacency list: an entry for each partition and each other node, with the distance to it
-type cu_al() :: [{cu_pair(), cu_dist()}].

%% adjacency matrix: the distances of an adjacency list per pair of nodes
-type cu_am() :: [{cu_pair(), [cu_dist()]}].

%% the adjacency matrix as a dict (DAM), as construct/3 keeps it
-type cu_dam() :: dict:dict(cu_pair(), [cu_dist()]).

%% the distances from the head of an ownership list to the first partition of other nodes
-type cu_node_dists() :: [{node(), cu_dist()}].

%% the completion test of construct/3: is the ownership list complete, and the length it has to reach
-type cu_complete() :: fun((cu_owners(), cu_dam()) -> {boolean(), non_neg_integer()}).

%% the score of an adjacency matrix (see rms/1), undefined for an empty matrix
-type cu_score() :: float() | undefined.

-type cu_violation_stat() :: {violations, non_neg_integer()}.
-type cu_balance_stat() :: {balance, non_neg_integer()} | {ownership, [{node(), pos_integer()}]}.
-type cu_diversity_stat() :: {diversity, cu_score()}.

%% the record load, no field has a type: node, num_pri, num_fb, norm_fb. The last one is the ratio
%% num_fb / all fallbacks, or the integer 0 if there is no fallback at all (norm_fb/2).
-type cu_load() :: {load, node(), non_neg_integer(), non_neg_integer(), float() | 0}.

%% the record failure, no field has a type: down, load, fbmin, fbmean, fbstddev, fb10, fb90, fbmax.
%% The module only reads it (the analysis that fills it is not part of riak_core_lite): fbmin and
%% fbmax are printed with ~b; fbmean, fbstddev, fb10 and fb90 are rounded with toint/1 first.
-type cu_failure() :: {failure, [node()], [cu_load()], non_neg_integer(), number(), number(), number(),
                       number(), non_neg_integer()}.

%% the second argument is target_n
-spec 'riak_core_claim_util:ring_stats'(riak_core_ring:riak_core_ring(), pos_integer()) ->
          [cu_violation_stat() | cu_balance_stat() | cu_diversity_stat()].
'riak_core_claim_util:ring_stats'(_, _) -> error(overlay).

-spec 'riak_core_claim_util:violation_stats'(riak_core_ring:riak_core_ring(), pos_integer()) ->
          [cu_violation_stat()].
'riak_core_claim_util:violation_stats'(_, _) -> error(overlay).

%% the balance is a sum of squares; an owner in the ownership count has at least one partition
-spec 'riak_core_claim_util:balance_stats'(riak_core_ring:riak_core_ring()) -> [cu_balance_stat()].
'riak_core_claim_util:balance_stats'(_) -> error(overlay).

-spec 'riak_core_claim_util:diversity_stats'(riak_core_ring:riak_core_ring(), pos_integer()) ->
          [cu_diversity_stat()].
'riak_core_claim_util:diversity_stats'(_, _) -> error(overlay).

%% the ring, the n_val of the preference lists, the nodes that are down
-spec 'riak_core_claim_util:node_load'(riak_core_ring:riak_core_ring(), pos_integer(), [node()]) -> [cu_load()].
'riak_core_claim_util:node_load'(_, _, _) -> error(overlay).

%% per node that is up the number of its primaries and of its fallbacks
-spec 'riak_core_claim_util:vnode_load'(riak_core_ring:riak_core_ring(), pos_integer(), [node()]) ->
          [{node(), non_neg_integer(), non_neg_integer()}].
'riak_core_claim_util:vnode_load'(_, _, _) -> error(overlay).

-spec 'riak_core_claim_util:norm_fb'(non_neg_integer(), non_neg_integer()) -> float() | 0.
'riak_core_claim_util:norm_fb'(_, _) -> error(overlay).

-spec 'riak_core_claim_util:print_analysis'([cu_failure()]) -> ok.
'riak_core_claim_util:print_analysis'(_) -> error(overlay).

-spec 'riak_core_claim_util:print_analysis'(io:device(), [cu_failure()]) -> ok.
'riak_core_claim_util:print_analysis'(_, _) -> error(overlay).

-spec 'riak_core_claim_util:print_analysis1'(io:device(), [cu_failure()]) -> ok.
'riak_core_claim_util:print_analysis1'(_, _) -> error(overlay).

%% two functions in one: a number is rounded, any other term is returned as it is. print_analysis1/2
%% needs the integer for ~b.
-spec 'riak_core_claim_util:toint'(number()) -> integer(); (term()) -> term().
'riak_core_claim_util:toint'(_) -> error(overlay).

-spec 'riak_core_claim_util:sort_by_down_fbmax'([cu_failure()]) -> [cu_failure()].
'riak_core_claim_util:sort_by_down_fbmax'(_) -> error(overlay).

-spec 'riak_core_claim_util:adjacency_matrix'(cu_owners()) -> cu_am().
'riak_core_claim_util:adjacency_matrix'(_) -> error(overlay).

%% the table is what ets:new/2 gives (a private duplicate_bag without name); the second argument
%% is a key of it or the end mark of ets:first/1 and ets:next/2
-spec 'riak_core_claim_util:adjacency_matrix_result'(ets:table(), cu_pair() | '$end_of_table', cu_am()) ->
          cu_am().
'riak_core_claim_util:adjacency_matrix_result'(_, _, _) -> error(overlay).

%% the table, the nodes of the ownership list, the rest of the list, the list twice from the same
%% position on
-spec 'riak_core_claim_util:adjacency_matrix_populate'(ets:table(), [node()], cu_owners(), cu_owners()) -> ok.
'riak_core_claim_util:adjacency_matrix_populate'(_, _, _, _) -> error(overlay).

%% the third argument has the nodes whose distance from Node is not known yet
-spec 'riak_core_claim_util:adjacency_matrix_add_dist'(ets:table(), node(), [node()], cu_owners(), cu_dist()) ->
          ok.
'riak_core_claim_util:adjacency_matrix_add_dist'(_, _, _, _, _) -> error(overlay).

%% the result has, per pair, the number of occurrences of the distances 0, 1, 2, ...
-spec 'riak_core_claim_util:summarize_am'(cu_am()) -> [{cu_pair(), [non_neg_integer()]}].
'riak_core_claim_util:summarize_am'(_) -> error(overlay).

-spec 'riak_core_claim_util:count_distances'([cu_dist()]) -> [non_neg_integer()].
'riak_core_claim_util:count_distances'(_) -> error(overlay).

-spec 'riak_core_claim_util:adjacency_matrix_from_al'(cu_al()) -> cu_am().
'riak_core_claim_util:adjacency_matrix_from_al'(_) -> error(overlay).

-spec 'riak_core_claim_util:adjacency_list'(cu_owners()) -> cu_al().
'riak_core_claim_util:adjacency_list'(_) -> error(overlay).

%% as adjacency_matrix_populate/4, with the result so far instead of the table
-spec 'riak_core_claim_util:adjacency_list'([node()], cu_owners(), cu_owners(), cu_al()) -> cu_al().
'riak_core_claim_util:adjacency_list'(_, _, _, _) -> error(overlay).

%% as adjacency_matrix_add_dist/5
-spec 'riak_core_claim_util:distances'(node(), [node()], cu_owners(), cu_dist(), cu_al()) -> cu_al().
'riak_core_claim_util:distances'(_, _, _, _, _) -> error(overlay).

%% the second argument is the n_val; with an n_val of 0 there is nothing to score and rms/1 throws
%% empty_list
-spec 'riak_core_claim_util:score_am'(cu_am(), pos_integer()) -> cu_score().
'riak_core_claim_util:score_am'(_, _) -> error(overlay).

%% the result is an orddict from the distance to the number of its occurrences, with an entry
%% for each distance below the n_val
-spec 'riak_core_claim_util:count'([cu_dist()], pos_integer()) -> [{cu_dist(), non_neg_integer()}].
'riak_core_claim_util:count'(_, _) -> error(overlay).

%% the sum of the squared differences to the mean, a float; throws empty_list for []
-spec 'riak_core_claim_util:rms'([number()]) -> float().
'riak_core_claim_util:rms'(_) -> error(overlay).

%% the ring has a partition per element and is made for the first one (hd/1)
-spec 'riak_core_claim_util:make_ring'([node(), ...]) -> riak_core_ring:riak_core_ring().
'riak_core_claim_util:make_ring'(_) -> error(overlay).

%% the argument has the distances that every pair of nodes must have
-spec 'riak_core_claim_util:gen_complete_diverse'([cu_dist()]) -> cu_complete().
'riak_core_claim_util:gen_complete_diverse'(_) -> error(overlay).

%% the length is compared with length/1 of the ownership list; riak_core_claim passes such a length
-spec 'riak_core_claim_util:gen_complete_len'(non_neg_integer()) -> cu_complete().
'riak_core_claim_util:gen_complete_len'(_) -> error(overlay).

%% the completion test, the members, the n_val. The first owner is lists:last/1 of the members,
%% so there must be one.
-spec 'riak_core_claim_util:construct'(cu_complete(), [node(), ...], pos_integer()) ->
          {ok, cu_owners(), cu_dam()}.
'riak_core_claim_util:construct'(_, _, _) -> error(overlay).

-spec 'riak_core_claim_util:empty_adjacency_matrix'([node()]) -> cu_dam().
'riak_core_claim_util:empty_adjacency_matrix'(_) -> error(overlay).

%% the members stand in for the eligible nodes of prepend_next_owner/5 if no node is eligible
-spec 'riak_core_claim_util:construct'(cu_complete(), [node(), ...], cu_owners(), cu_dam(), pos_integer()) ->
          {ok, cu_owners(), cu_dam()}.
'riak_core_claim_util:construct'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_claim_util:met_required'(cu_owners(), cu_dam(), [cu_dist()]) -> boolean().
'riak_core_claim_util:met_required'(_, _, _) -> error(overlay).

-spec 'riak_core_claim_util:next_pow2'(non_neg_integer()) -> pos_integer().
'riak_core_claim_util:next_pow2'(_) -> error(overlay).

-spec 'riak_core_claim_util:next_pow2'(non_neg_integer(), pos_integer()) -> pos_integer().
'riak_core_claim_util:next_pow2'(_, _) -> error(overlay).

%% the members, the ones that may own the next partition, the owners so far, their matrix, the n_val.
%% The fold starts with undefined for the best score, the owners and the matrix; the first eligible
%% node replaces them, because a number is smaller than an atom. So there must be an eligible node.
-spec 'riak_core_claim_util:prepend_next_owner'([node()], [node(), ...], cu_owners(), cu_dam(), pos_integer()) ->
          {cu_owners(), cu_dam()}.
'riak_core_claim_util:prepend_next_owner'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_claim_util:prepend'([node()], node(), cu_owners(), cu_dam()) -> {cu_owners(), cu_dam()}.
'riak_core_claim_util:prepend'(_, _, _, _) -> error(overlay).

%% the first argument has the nodes to look for
-spec 'riak_core_claim_util:distances2'([node()], cu_owners()) -> cu_node_dists().
'riak_core_claim_util:distances2'(_, _) -> error(overlay).

-spec 'riak_core_claim_util:distances2'([node()], cu_owners(), cu_dist(), cu_node_dists()) -> cu_node_dists().
'riak_core_claim_util:distances2'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claim_util:fixup_dam'(cu_owners(), cu_dam()) -> cu_dam().
'riak_core_claim_util:fixup_dam'(_, _) -> error(overlay).

%% the nodes that are not fixed yet, the reversed ownership list, the ownership list, the distance
%% from the current partition to the end of the list
-spec 'riak_core_claim_util:fixup_dam'([node()], cu_owners(), cu_owners(), cu_dist(), cu_dam()) -> cu_dam().
'riak_core_claim_util:fixup_dam'(_, _, _, _, _) -> error(overlay).

%% K out of N; there is a clause only for K =< N
-spec 'riak_core_claim_util:num_perms'(non_neg_integer(), non_neg_integer()) -> pos_integer().
'riak_core_claim_util:num_perms'(_, _) -> error(overlay).

%% as num_perms/2. The code divides by K * fac(N - K), not by fac(K) * fac(N - K).
-spec 'riak_core_claim_util:num_combs'(non_neg_integer(), non_neg_integer()) -> pos_integer().
'riak_core_claim_util:num_combs'(_, _) -> error(overlay).

-spec 'riak_core_claim_util:fac'(non_neg_integer()) -> pos_integer().
'riak_core_claim_util:fac'(_) -> error(overlay).

%% works for any list; substitutions/2 calls it with names of nodes
-spec 'riak_core_claim_util:perm_gen'([T]) -> [[T]].
'riak_core_claim_util:perm_gen'(_) -> error(overlay).

-spec 'riak_core_claim_util:down_combos'(non_neg_integer(), [node()]) -> [[node()]].
'riak_core_claim_util:down_combos'(_, _) -> error(overlay).

%% the third argument has the combinations so far
-spec 'riak_core_claim_util:down_combos'(non_neg_integer(), [node()], [[node()]]) -> [[node()]].
'riak_core_claim_util:down_combos'(_, _, _) -> error(overlay).

%% the only clause is for a list with a head
-spec 'riak_core_claim_util:rotations'([node(), ...]) -> [[node(), ...]].
'riak_core_claim_util:rotations'(_) -> error(overlay).

%% the number of rotations that are missing, the next rotation, the rotations so far
-spec 'riak_core_claim_util:rotations'(non_neg_integer(), [node(), ...], [[node(), ...]]) -> [[node(), ...]].
'riak_core_claim_util:rotations'(_, _, _) -> error(overlay).

%% an ownership list and the names in it; the result has a list per permutation of the names
-spec 'riak_core_claim_util:substitutions'(cu_owners(), [node()]) -> [cu_owners()].
'riak_core_claim_util:substitutions'(_, _) -> error(overlay).

%% the names, their replacements in the same order, the ownership list
-spec 'riak_core_claim_util:substitute'([node()], [node()], cu_owners()) -> cu_owners().
'riak_core_claim_util:substitute'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_claimant
%% ---------------------------------------------------------------------------------------------

%% what can be staged for a node. action() and the changes field of the state name only the first four;
%% resize_ring/1 and abort_resize/0 stage the other two through the same stage/2.
-type cl_action() :: riak_core_claimant:action() | {resize, integer()} | abort_resize.

%% the staged changes, an orddict from the node to its action (the changes field of the state)
-type cl_changes() :: [{node(), cl_action()}].

%% the changes of a plan: the staged ones and a join for every joining member (generate_plan/2),
%% sorted by node
-type cl_plan_changes() :: [{node(), cl_action() | join}].

%% the nodes that are replaced and their replacements, an orddict (remove_node/7 looks a node up in it)
-type cl_replacing() :: [{node(), node()}].

%% the seed of riak_core_rand:rand_seed/0, kept so that plan and commit remove nodes in the same way
-type cl_seed() :: erlang:timestamp().

%% the id of the ring in riak_core_ring_manager (get_ring_id/0): epoch and counter
-type cl_ring_id() :: {non_neg_integer(), non_neg_integer()}.

%% the record state: last_ring_id, changes, next_ring, seed. last_ring_id and seed have no type in the
%% record; last_ring_id is undefined until the first tick and after reset_ring_id.
-type cl_state() :: {state,
                     cl_ring_id() | undefined,
                     [{node(), riak_core_claimant:action()}],
                     riak_core_claimant:riak_core_ring() | undefined,
                     cl_seed()}.

%% why a request is not staged (the valid_*_request functions)
-type cl_stage_error() :: {error, not_member | only_member | already_leaving | is_claimant
                                  | already_replacement | invalid_replacement
                                  | same_size | single_node | pending_changes | not_resizing}.

%% why maybe_commit_staged/2,3 leave the ring as it is
-type cl_ignore_reason() :: invalid_resize_claim | ring_not_ready | plan_changed.

%% an element of the list of pending ownership changes of a ring: index, owner, next owner ('$resize'
%% while the ring is resized), the modules whose handoff is complete, status. riak_core_ring has no name
%% for it. The next field of its chstate record says term() for the two owners; they are nodes here, as
%% in riak_core_ring:pending_change(): the claimant compares them with the members of the ring.
-type cl_next() :: {chash:index_as_int(), node(), node(), [module()], awaiting | complete}.

%% a Log fun (log/2 or no_log/2) gets the kind of the event and its data:
%%   debug: format and arguments
%%   ownership, reassign: index, new owner, ring
%%   next: index, owner, next owner
%% A fun type cannot say which data belongs to which kind, so this is the union.
-type cl_log_data() :: {string(), [term()]}
                     | {chash:index_as_int(), node(), riak_core_claimant:riak_core_ring()}
                     | {chash:index_as_int(), node(), node()}.
-type cl_log() :: fun((debug | ownership | reassign | next, cl_log_data()) -> ok).

-spec 'riak_core_claimant:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_claimant:start_link'() -> error(overlay).

%% the four requests have the result of resize_ring/1 and abort_resize/0, which have a spec
-spec 'riak_core_claimant:leave_member'(node()) -> ok | {error, atom()}.
'riak_core_claimant:leave_member'(_) -> error(overlay).

-spec 'riak_core_claimant:remove_member'(node()) -> ok | {error, atom()}.
'riak_core_claimant:remove_member'(_) -> error(overlay).

-spec 'riak_core_claimant:replace'(node(), node()) -> ok | {error, atom()}.
'riak_core_claimant:replace'(_, _) -> error(overlay).

-spec 'riak_core_claimant:force_replace'(node(), node()) -> ok | {error, atom()}.
'riak_core_claimant:force_replace'(_, _) -> error(overlay).

-spec 'riak_core_claimant:clear'() -> ok.
'riak_core_claimant:clear'() -> error(overlay).

%% the first argument is the node that runs the claimant logic (riak_core_ring:ring_changed/2)
-spec 'riak_core_claimant:ring_changed'(node(), riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:ring_changed'(_, _) -> error(overlay).

%% true if the owners or the pending changes are different in the new ring
-spec 'riak_core_claimant:reassign_indices'(riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:reassign_indices'(_) -> error(overlay).

-spec 'riak_core_claimant:stage'(node(), cl_action()) -> ok | {error, atom()}.
'riak_core_claimant:stage'(_, _) -> error(overlay).

%% the server of the node that is the claimant, as a destination of gen_server:call
-spec 'riak_core_claimant:claimant'() -> {riak_core_claimant, node()}.
'riak_core_claimant:claimant'() -> error(overlay).

-spec 'riak_core_claimant:init'([]) -> {ok, cl_state()}.
'riak_core_claimant:init'(_) -> error(overlay).

%% the replies: clear and unknown requests ok, stage ok | cl_stage_error(), plan the changes and the
%% transitions or an error, commit ok | error | {error, _}. The bare error (not the claimant) is not in
%% the spec of commit/0.
-spec 'riak_core_claimant:handle_call'(term(), {pid(), term()}, cl_state()) ->
          {reply,
           ok | error | cl_stage_error()
           | {error, nothing_planned | cl_ignore_reason()}
           | {ok, cl_plan_changes(), [riak_core_claimant:ring_transition()]},
           cl_state()}.
'riak_core_claimant:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:handle_cast'(term(), cl_state()) -> {noreply, cl_state()}.
'riak_core_claimant:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_claimant:handle_info'(term(), cl_state()) -> {noreply, cl_state()}.
'riak_core_claimant:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_claimant:terminate'(term(), cl_state()) -> ok.
'riak_core_claimant:terminate'(_, _) -> error(overlay).

-spec 'riak_core_claimant:code_change'(term(), cl_state(), term()) -> {ok, cl_state()}.
'riak_core_claimant:code_change'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_stage'(node(), cl_action(), riak_core_claimant:riak_core_ring(), cl_state()) ->
          {ok | cl_stage_error(), cl_state()}.
'riak_core_claimant:maybe_stage'(_, _, _, _) -> error(overlay).

%% the reply of plan and the state with the planned ring
-spec 'riak_core_claimant:generate_plan'(riak_core_claimant:riak_core_ring(), cl_state()) ->
          {{ok, cl_plan_changes(), [riak_core_claimant:ring_transition()]} | {error, invalid_resize_claim},
           cl_state()}.
'riak_core_claimant:generate_plan'(_, _) -> error(overlay).

-spec 'riak_core_claimant:generate_plan'(cl_plan_changes(), riak_core_claimant:riak_core_ring(), cl_state()) ->
          {{ok, cl_plan_changes(), [riak_core_claimant:ring_transition()]} | {error, invalid_resize_claim},
           cl_state()}.
'riak_core_claimant:generate_plan'(_, _, _) -> error(overlay).

%% the reply of commit and the new state. error: this node is not the claimant (ring_trans says not_changed)
-spec 'riak_core_claimant:commit_staged'(cl_state()) ->
          {ok | error | {error, nothing_planned | cl_ignore_reason()}, cl_state()}.
'riak_core_claimant:commit_staged'(_) -> error(overlay).

%% the result of riak_core_ring_manager:ring_trans/2 for the fun maybe_commit_staged/2
-spec 'riak_core_claimant:maybe_commit_staged'(cl_state()) ->
          {ok, riak_core_claimant:riak_core_ring()} | not_changed | {not_changed, cl_ignore_reason()}.
'riak_core_claimant:maybe_commit_staged'(_) -> error(overlay).

%% a fun for ring_trans/2: the raw ring and the argument
-spec 'riak_core_claimant:maybe_commit_staged'(riak_core_claimant:riak_core_ring(), cl_state()) ->
          {new_ring, riak_core_claimant:riak_core_ring()} | ignore | {ignore, cl_ignore_reason()}.
'riak_core_claimant:maybe_commit_staged'(_, _) -> error(overlay).

%% the ring, the ring after the staged changes, the state with the planned ring
-spec 'riak_core_claimant:maybe_commit_staged'(riak_core_claimant:riak_core_ring(),
                                               riak_core_claimant:riak_core_ring(), cl_state()) ->
          {new_ring, riak_core_claimant:riak_core_ring()} | ignore | {ignore, ring_not_ready | plan_changed}.
'riak_core_claimant:maybe_commit_staged'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:clear_staged'(cl_state()) -> cl_state().
'riak_core_claimant:clear_staged'(_) -> error(overlay).

%% the result of ring_trans/2 for the fun remove_joining_nodes/2
-spec 'riak_core_claimant:remove_joining_nodes'() -> {ok, riak_core_claimant:riak_core_ring()} | not_changed.
'riak_core_claimant:remove_joining_nodes'() -> error(overlay).

%% a fun for ring_trans/2; the second argument is not used, remove_joining_nodes/0 gives ok
-spec 'riak_core_claimant:remove_joining_nodes'(riak_core_claimant:riak_core_ring(), ok) ->
          ignore | {new_ring, riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:remove_joining_nodes'(_, _) -> error(overlay).

%% the claimant, the joining nodes, the ring
-spec 'riak_core_claimant:remove_joining_nodes_from_ring'(node(), [node()], riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:remove_joining_nodes_from_ring'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:valid_request'(node(), cl_action(), cl_changes(), riak_core_claimant:riak_core_ring()) ->
          true | cl_stage_error().
'riak_core_claimant:valid_request'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:valid_leave_request'(node(), riak_core_claimant:riak_core_ring()) ->
          true | {error, not_member | only_member | already_leaving}.
'riak_core_claimant:valid_leave_request'(_, _) -> error(overlay).

-spec 'riak_core_claimant:valid_remove_request'(node(), riak_core_claimant:riak_core_ring()) ->
          true | {error, is_claimant | not_member | only_member}.
'riak_core_claimant:valid_remove_request'(_, _) -> error(overlay).

%% the node, its replacement, the staged changes, the ring
-spec 'riak_core_claimant:valid_replace_request'(node(), node(), cl_changes(),
                                                 riak_core_claimant:riak_core_ring()) ->
          true | {error, not_member | already_leaving | already_replacement | invalid_replacement}.
'riak_core_claimant:valid_replace_request'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:valid_force_replace_request'(node(), node(), cl_changes(),
                                                       riak_core_claimant:riak_core_ring()) ->
          true | {error, is_claimant | not_member | already_replacement | invalid_replacement}.
'riak_core_claimant:valid_force_replace_request'(_, _, _, _) -> error(overlay).

%% the second argument is the staged changes that valid_request/4 hands over. The only clause is for [],
%% a resize together with other staged changes ends in a function_clause error.
-spec 'riak_core_claimant:valid_resize_request'(integer(), cl_changes(), riak_core_claimant:riak_core_ring()) ->
          true | {error, same_size | single_node | pending_changes}.
'riak_core_claimant:valid_resize_request'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:valid_resize_abort_request'(riak_core_claimant:riak_core_ring()) ->
          true | {error, not_resizing}.
'riak_core_claimant:valid_resize_abort_request'(_) -> error(overlay).

-spec 'riak_core_claimant:filter_changes'(cl_changes(), riak_core_claimant:riak_core_ring()) -> cl_changes().
'riak_core_claimant:filter_changes'(_, _) -> error(overlay).

%% is the change of the node still valid, given all staged changes and the ring
-spec 'riak_core_claimant:filter_changes_pred'(node(), cl_action(), cl_changes(),
                                               riak_core_claimant:riak_core_ring()) -> boolean().
'riak_core_claimant:filter_changes_pred'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:existing_replacements'(cl_changes()) -> [node()].
'riak_core_claimant:existing_replacements'(_) -> error(overlay).

-spec 'riak_core_claimant:same_plan'(riak_core_claimant:riak_core_ring(), riak_core_claimant:riak_core_ring()) ->
          boolean().
'riak_core_claimant:same_plan'(_, _) -> error(overlay).

%% the timer of erlang:send_after/3
-spec 'riak_core_claimant:schedule_tick'() -> reference().
'riak_core_claimant:schedule_tick'() -> error(overlay).

-spec 'riak_core_claimant:tick'(cl_state()) -> cl_state().
'riak_core_claimant:tick'(_) -> error(overlay).

-spec 'riak_core_claimant:maybe_force_ring_update'(riak_core_claimant:riak_core_ring()) -> ok.
'riak_core_claimant:maybe_force_ring_update'(_) -> error(overlay).

-spec 'riak_core_claimant:do_maybe_force_ring_update'(riak_core_claimant:riak_core_ring()) -> ok.
'riak_core_claimant:do_maybe_force_ring_update'(_) -> error(overlay).

%% one transition per round of rebalancing. The list is never empty (generate_plan/3 takes its head);
%% the type is the one of plan/0.
-spec 'riak_core_claimant:compute_all_next_rings'(cl_plan_changes(), cl_seed(),
                                                  riak_core_claimant:riak_core_ring()) ->
          {ok, [riak_core_claimant:ring_transition()]} | {error, invalid_resize_claim}.
'riak_core_claimant:compute_all_next_rings'(_, _, _) -> error(overlay).

%% the fourth argument is the transitions so far, the last one first
-spec 'riak_core_claimant:compute_all_next_rings'(cl_plan_changes(), cl_seed(),
                                                  riak_core_claimant:riak_core_ring(),
                                                  [riak_core_claimant:ring_transition()]) ->
          {ok, [riak_core_claimant:ring_transition()]} | {error, invalid_resize_claim}.
'riak_core_claimant:compute_all_next_rings'(_, _, _, _) -> error(overlay).

%% the changes are those of a plan (with joins), the staged ones (commit) or none (tick)
-spec 'riak_core_claimant:compute_next_ring'(cl_plan_changes(), cl_seed(), riak_core_claimant:riak_core_ring()) ->
          {ok, riak_core_claimant:riak_core_ring()} | {error, invalid_resize_claim}.
'riak_core_claimant:compute_next_ring'(_, _, _) -> error(overlay).

%% the installed ring and the ring after the changes; false if the resized ring is not claimed properly
-spec 'riak_core_claimant:maybe_compute_resize'(riak_core_claimant:riak_core_ring(),
                                                riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_compute_resize'(_, _) -> error(overlay).

-spec 'riak_core_claimant:compute_resize'(riak_core_claimant:riak_core_ring(),
                                          riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:compute_resize'(_, _) -> error(overlay).

%% an index of the old ring with its owner, and the owner of the index in the resized ring, none if the
%% index is not in it (a ring that shrinks)
-spec 'riak_core_claimant:schedule_first_resize_transfer'(larger | smaller, {chash:index_as_int(), node()},
                                                          node() | none,
                                                          riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:schedule_first_resize_transfer'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:validate_resized_ring'(riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:validate_resized_ring'(_) -> error(overlay).

-spec 'riak_core_claimant:apply_changes'(riak_core_claimant:riak_core_ring(), cl_plan_changes()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:apply_changes'(_, _) -> error(overlay).

%% a change the other way round: the action and the node. Throws invalid_member for a leave or remove of
%% a node that is not a member.
-spec 'riak_core_claimant:change'({cl_action() | join, node()}, riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:change'(_, _) -> error(overlay).

-spec 'riak_core_claimant:internal_ring_changed'(node(), riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:internal_ring_changed'(_, _) -> error(overlay).

%% this node, the ring before and the ring after the claimant logic
-spec 'riak_core_claimant:inform_removed_nodes'(node(), riak_core_claimant:riak_core_ring(),
                                                riak_core_claimant:riak_core_ring()) -> ok.
'riak_core_claimant:inform_removed_nodes'(_, _, _) -> error(overlay).

%% do_claimant: true if the ring is changed
-spec 'riak_core_claimant:do_claimant_quiet'(node(), riak_core_claimant:riak_core_ring(), cl_replacing(),
                                             cl_seed()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:do_claimant_quiet'(_, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:do_claimant'(node(), riak_core_claimant:riak_core_ring(), cl_log()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:do_claimant'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:do_claimant'(node(), riak_core_claimant:riak_core_ring(), cl_replacing(), cl_seed(),
                                       cl_log()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:do_claimant'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_update_claimant'(node(), riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_update_claimant'(_, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_update_ring'(node(), riak_core_claimant:riak_core_ring(), cl_replacing(),
                                             cl_seed(), cl_log()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_update_ring'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_remove_exiting'(node(), riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_remove_exiting'(_, _) -> error(overlay).

-spec 'riak_core_claimant:are_joining_nodes'(riak_core_claimant:riak_core_ring()) -> boolean().
'riak_core_claimant:are_joining_nodes'(_) -> error(overlay).

%% the joining members with the meta data '$autojoin'
-spec 'riak_core_claimant:auto_joining_nodes'(riak_core_claimant:riak_core_ring()) -> [node()].
'riak_core_claimant:auto_joining_nodes'(_) -> error(overlay).

-spec 'riak_core_claimant:maybe_handle_auto_joining'(node(), riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_handle_auto_joining'(_, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_handle_joining'(node(), riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_handle_joining'(_, _) -> error(overlay).

%% the second argument is the joining nodes that become valid
-spec 'riak_core_claimant:maybe_handle_joining'(node(), [node()], riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_handle_joining'(_, _, _) -> error(overlay).

%% the last argument: is the ring being resized
-spec 'riak_core_claimant:update_ring'(node(), riak_core_claimant:riak_core_ring(), cl_replacing(), cl_seed(),
                                       cl_log(), boolean()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:update_ring'(_, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_claimant:maybe_install_resized_ring'(riak_core_claimant:riak_core_ring()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:maybe_install_resized_ring'(_) -> error(overlay).

-spec 'riak_core_claimant:transfer_ownership'(riak_core_claimant:riak_core_ring(), cl_log()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:transfer_ownership'(_, _) -> error(overlay).

-spec 'riak_core_claimant:reassign_indices'(riak_core_claimant:riak_core_ring(), cl_replacing(), cl_seed(),
                                            cl_log()) ->
          {boolean(), riak_core_claimant:riak_core_ring()}.
'riak_core_claimant:reassign_indices'(_, _, _, _) -> error(overlay).

%% the pending changes of the ring, or those of a new claim if there are none
-spec 'riak_core_claimant:rebalance_ring'(node(), riak_core_claimant:riak_core_ring()) -> [cl_next()].
'riak_core_claimant:rebalance_ring'(_, _) -> error(overlay).

-spec 'riak_core_claimant:rebalance_ring'(node(), [cl_next()], riak_core_claimant:riak_core_ring()) ->
          [cl_next()].
'riak_core_claimant:rebalance_ring'(_, _, _) -> error(overlay).

-spec 'riak_core_claimant:handle_down_nodes'(riak_core_claimant:riak_core_ring(), [cl_next()]) -> [cl_next()].
'riak_core_claimant:handle_down_nodes'(_, _) -> error(overlay).

%% the indices of the node go to the new node
-spec 'riak_core_claimant:reassign_indices_to'(node(), node(), riak_core_claimant:riak_core_ring()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:reassign_indices_to'(_, _, _) -> error(overlay).

%% the third argument is the status of the node, reassign_indices/4 removes invalid and leaving members
-spec 'riak_core_claimant:remove_node'(riak_core_claimant:riak_core_ring(), node(), invalid | leaving,
                                       cl_replacing(), cl_seed(), cl_log()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:remove_node'(_, _, _, _, _, _) -> error(overlay).

%% the last argument is the indices of the node
-spec 'riak_core_claimant:remove_node'(riak_core_claimant:riak_core_ring(), node(), invalid | leaving,
                                       cl_replacing(), cl_seed(), cl_log(), [chash:index_as_int()]) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:remove_node'(_, _, _, _, _, _, _) -> error(overlay).

%% the ring, the node, its replacement
-spec 'riak_core_claimant:replace_node_during_resize'(riak_core_claimant:riak_core_ring(), node(), node()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:replace_node_during_resize'(_, _, _) -> error(overlay).

%% the last argument: is the resize in its cleanup phase (riak_core_ring:is_post_resize/1)
-spec 'riak_core_claimant:replace_node_during_resize'(riak_core_claimant:riak_core_ring(), node(), node(),
                                                      boolean()) ->
          riak_core_claimant:riak_core_ring().
'riak_core_claimant:replace_node_during_resize'(_, _, _, _) -> error(overlay).

%% the two Log funs, see cl_log()
-spec 'riak_core_claimant:no_log'(debug | ownership | reassign | next, cl_log_data()) -> ok.
'riak_core_claimant:no_log'(_, _) -> error(overlay).

-spec 'riak_core_claimant:log'(debug | ownership | reassign | next, cl_log_data()) -> ok.
'riak_core_claimant:log'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode
%% ---------------------------------------------------------------------------------------------

%% the target of a handoff: the field handoff_target without none
-type vn_target() :: {riak_core_vnode:partition(), node()}.
%% the field forward: undefined (an atom, like every node()) for no forwarding, the next owner after a
%% handoff, or during a resize the targets of the transfers that are complete.
%% The record says node() | [{integer(), node()}], which is the same type.
-type vn_forward() :: undefined | node() | [vn_target()].
%% the indexes that a resize transfer has seen and not sent, an ordsets:ordset() of the handoff sender
-type vn_seen_idxs() :: [riak_core_vnode:partition()].
%% the names of the states of the fsm
-type vn_state_name() :: started | active.
%% what a vnode tells the vnode manager again and again until that answers (inactive is sent only once)
-type vn_manager_event() :: handoff_complete | handoff_error.

%% the request records of riak_core_vnode.hrl as tuples
-type vn_vnode_req() :: {riak_vnode_req_v1, riak_core_vnode:partition() | undefined, riak_core_vnode:sender(),
                         riak_core_vnode:vnode_req()}.
-type vn_coverage_req() :: {riak_coverage_req_v1, riak_core_vnode:partition(), riak_core_vnode:keyspaces(),
                            riak_core_vnode:sender(), riak_core_vnode:vnode_req()}.

%% the vnode goes on in the state active, with the inactivity timeout
-type vn_next() :: {next_state, active, riak_core_vnode:state(), non_neg_integer()}.
%% a callback of the vnode module can stop the vnode
-type vn_result() :: vn_next() | {stop, term(), riak_core_vnode:state()}.

%% the reply to core_status: the mode (undefined: forwarding and a handoff target at once) and the fields of
%% the state that are set
-type vn_core_status() :: {active | handoff | forward | undefined,
                           [{index, riak_core_vnode:partition()} | {mod, module()} |
                            {forward, node() | [vn_target()]} | {handoff_target, vn_target()} | deleted]}.

%% [Mod, Index, InitialInactivityTimeout, Forward]
-type vn_init_args() :: [module() | riak_core_vnode:partition() | non_neg_integer() | vn_forward()].

%% the child of riak_core_vnode_sup, started with [Mod, Index, ForwardTo]
-spec 'riak_core_vnode:start_link'(module(), riak_core_vnode:partition(), vn_forward()) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode:start_link'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:start_link'(module(), riak_core_vnode:partition(), non_neg_integer(), vn_forward()) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode:start_link'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode:send_command'(pid(), riak_core_vnode:vnode_req()) -> ok.
'riak_core_vnode:send_command'(_, _) -> error(overlay).

-spec 'riak_core_vnode:init'(vn_init_args()) -> {ok, started, riak_core_vnode:state(), 0}.
'riak_core_vnode:init'(_) -> error(overlay).

%% {stop, Reason} is what the code gives back if the init of the vnode module fails. gen_fsm_compat does not
%% know this form (it wants {stop, Reason, StateData}) and ends with bad_return_value.
-spec 'riak_core_vnode:started'(timeout, riak_core_vnode:state()) -> vn_next() | {stop, term()}.
'riak_core_vnode:started'(_, _) -> error(overlay).

-spec 'riak_core_vnode:started'(wait_for_init, {pid(), term()}, riak_core_vnode:state()) ->
          {reply, ok, active, riak_core_vnode:state(), non_neg_integer()} | {stop, term()}.
'riak_core_vnode:started'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:do_init'(riak_core_vnode:state()) -> {ok, riak_core_vnode:state()} | {error, term()}.
'riak_core_vnode:do_init'(_) -> error(overlay).

%% started/3 and active/3 both reply ok
-spec 'riak_core_vnode:wait_for_init'(pid()) -> ok.
'riak_core_vnode:wait_for_init'(_) -> error(overlay).

%% the vnode looks neither at the kind of the error nor at the reason. The kind is 'DOWN' from the handoff
%% manager; the handoff sender sends the same event with fold_error or the class of an exception.
-spec 'riak_core_vnode:handoff_error'(pid(), atom(), term()) -> ok.
'riak_core_vnode:handoff_error'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:get_mod_index'(pid()) -> {module(), riak_core_vnode:partition()}.
'riak_core_vnode:get_mod_index'(_) -> error(overlay).

-spec 'riak_core_vnode:set_forwarding'(pid(), vn_forward()) -> ok.
'riak_core_vnode:set_forwarding'(_, _) -> error(overlay).

-spec 'riak_core_vnode:trigger_handoff'(pid(), riak_core_vnode:partition(), node()) -> ok.
'riak_core_vnode:trigger_handoff'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:trigger_handoff'(pid(), node()) -> ok.
'riak_core_vnode:trigger_handoff'(_, _) -> error(overlay).

-spec 'riak_core_vnode:trigger_delete'(pid()) -> ok.
'riak_core_vnode:trigger_delete'(_) -> error(overlay).

-spec 'riak_core_vnode:core_status'(pid()) -> vn_core_status().
'riak_core_vnode:core_status'(_) -> error(overlay).

-spec 'riak_core_vnode:continue'(riak_core_vnode:state()) -> vn_next().
'riak_core_vnode:continue'(_) -> error(overlay).

%% the second argument is the new state of the vnode module
-spec 'riak_core_vnode:continue'(riak_core_vnode:state(), term()) -> vn_next().
'riak_core_vnode:continue'(_, _) -> error(overlay).

-spec 'riak_core_vnode:forward_or_vnode_command'(riak_core_vnode:sender(), riak_core_vnode:vnode_req(),
                                                 riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:forward_or_vnode_command'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:vnode_command'(riak_core_vnode:sender(), riak_core_vnode:vnode_req(),
                                      riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:vnode_command'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:vnode_coverage'(riak_core_vnode:sender(), riak_core_vnode:vnode_req(),
                                       riak_core_vnode:keyspaces(), riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:vnode_coverage'(_, _, _, _) -> error(overlay).

%% the third argument is where a request goes that the vnode module wants to have forwarded during a resize
-spec 'riak_core_vnode:vnode_handoff_command'(riak_core_vnode:sender(), riak_core_vnode:vnode_req(), vn_target(),
                                              riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:vnode_handoff_command'(_, _, _, _) -> error(overlay).

%% the handoff type is undefined and the handoff target none if a resize is going on, but no transfer;
%% the result is the one of riak_core_vnode_master:command_unreliable/4
-spec 'riak_core_vnode:forward_request'(riak_core_handoff_manager:ho_type() | undefined,
                                        riak_core_vnode:vnode_req(), none | vn_target(), vn_target(),
                                        riak_core_vnode:sender(), riak_core_vnode:state()) -> ok.
'riak_core_vnode:forward_request'(_, _, _, _, _, _) -> error(overlay).

%% the first argument is only logged
-spec 'riak_core_vnode:vnode_forward'(implicit | explicit | resize, vn_target(), riak_core_vnode:sender(),
                                      riak_core_vnode:vnode_req(), riak_core_vnode:state()) -> ok.
'riak_core_vnode:vnode_forward'(_, _, _, _, _) -> error(overlay).

%% the future index is the result of riak_core_ring:future_index/3: undefined if the key has no place in the
%% ring after the resize, the command is then handled by this vnode
-spec 'riak_core_vnode:vnode_resize_command'(riak_core_vnode:sender(), riak_core_vnode:vnode_req(),
                                             riak_core_vnode:partition() | undefined, riak_core_vnode:state()) ->
          vn_result().
'riak_core_vnode:vnode_resize_command'(_, _, _, _) -> error(overlay).

%% no catch-all clause: the events that the vnode proxy and master (requests, unregistered), the handoff
%% sender and manager, the vnode manager (through handle_event/3) and the vnode itself (timer) send
-spec 'riak_core_vnode:active'(timeout | vn_coverage_req() | vn_vnode_req() | handoff_complete |
                               {resize_transfer_complete, vn_seen_idxs()} | {handoff_error, atom(), term()} |
                               {send_manager_event, vn_manager_event()} | {trigger_handoff, node()} |
                               {trigger_handoff, riak_core_vnode:partition(), node()} | trigger_delete |
                               unregistered,
                               riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:active'(_, _) -> error(overlay).

-spec 'riak_core_vnode:active'(term(), {pid(), term()}, riak_core_vnode:state()) ->
          {reply, ok, active, riak_core_vnode:state(), non_neg_integer()}.
'riak_core_vnode:active'(_, _, _) -> error(overlay).

%% a transfer of a resize gives resize or continue, a handoff to the next owner one of the other three
-spec 'riak_core_vnode:mark_handoff_complete'(riak_core_vnode:partition(), vn_target(), vn_seen_idxs(), module(),
                                              riak_core_handoff_manager:ho_type()) ->
          continue | resize | forward | shutdown.
'riak_core_vnode:mark_handoff_complete'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_vnode:finish_handoff'(riak_core_vnode:state()) -> vn_next().
'riak_core_vnode:finish_handoff'(_) -> error(overlay).

-spec 'riak_core_vnode:finish_handoff'(vn_seen_idxs(), riak_core_vnode:state()) -> vn_next().
'riak_core_vnode:finish_handoff'(_, _) -> error(overlay).

%% the result of riak_core_vnode_worker_pool:shutdown_pool/2, ok without a pool
-spec 'riak_core_vnode:maybe_shutdown_pool'(riak_core_vnode:state()) -> ok | {error, vnode_shutdown}.
'riak_core_vnode:maybe_shutdown_pool'(_) -> error(overlay).

-spec 'riak_core_vnode:resize_forwarding'(riak_core_vnode:state()) -> [vn_target()].
'riak_core_vnode:resize_forwarding'(_) -> error(overlay).

%% the result of riak_core_ring_manager:ring_trans/2 for a fun that gives {set_only, Ring} or ignore
-spec 'riak_core_vnode:mark_delete_complete'(riak_core_vnode:partition(), module()) ->
          {ok, riak_core_ring:riak_core_ring()} | not_changed.
'riak_core_vnode:mark_delete_complete'(_, _) -> error(overlay).

%% no catch-all clause: the events of set_forwarding/2, trigger_handoff/2,3 and trigger_delete/1, the answers
%% of the vnode manager to a vn_manager_event(), and requests (riak_core_vnode_master sends the one of
%% sync_spawn_command as an event for all states)
-spec 'riak_core_vnode:handle_event'({set_forwarding, vn_forward()} | finish_handoff | cancel_handoff |
                                     {trigger_handoff, node()} |
                                     {trigger_handoff, riak_core_vnode:partition(), node()} | trigger_delete |
                                     vn_vnode_req() | vn_coverage_req(),
                                     vn_state_name(), riak_core_vnode:state()) -> vn_result().
'riak_core_vnode:handle_event'(_, _, _) -> error(overlay).

%% no catch-all clause. The reply to current_state has no timeout, the others keep the inactivity timeout;
%% the replies are {Mod, Index} to get_mod_index, the answer of the vnode module (or vnode_exiting) to
%% handoff_data, and the status to core_status.
-spec 'riak_core_vnode:handle_sync_event'(current_state | get_mod_index | {handoff_data, binary()} | core_status,
                                          {pid(), term()}, vn_state_name(), riak_core_vnode:state()) ->
          {reply, {vn_state_name(), riak_core_vnode:state()}, vn_state_name(), riak_core_vnode:state()} |
          {reply, {module(), riak_core_vnode:partition()} | ok | {error, term()} | vn_core_status(),
           vn_state_name(), riak_core_vnode:state(), non_neg_integer()}.
'riak_core_vnode:handle_sync_event'(_, _, _, _) -> error(overlay).

%% the last clause takes every message and gives it to the vnode module
-spec 'riak_core_vnode:handle_info'(term(), vn_state_name(), riak_core_vnode:state()) ->
          {next_state, vn_state_name(), riak_core_vnode:state(), non_neg_integer()} |
          {stop, term(), riak_core_vnode:state()}.
'riak_core_vnode:handle_info'(_, _, _) -> error(overlay).

%% the value of the try: the result of riak_core_vnode_worker_pool:shutdown_pool/2, or ok
-spec 'riak_core_vnode:terminate'(term(), vn_state_name(), riak_core_vnode:state()) ->
          ok | {error, vnode_shutdown}.
'riak_core_vnode:terminate'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode:code_change'(term(), vn_state_name(), riak_core_vnode:state(), term()) ->
          {ok, vn_state_name(), riak_core_vnode:state()}.
'riak_core_vnode:code_change'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode:maybe_handoff'(riak_core_vnode:partition(), node(), riak_core_vnode:state()) -> vn_next().
'riak_core_vnode:maybe_handoff'(_, _, _) -> error(overlay).

%% maybe_handoff/3 calls it with resize, ownership or hinted
-spec 'riak_core_vnode:start_handoff'(riak_core_handoff_manager:ho_type(), riak_core_vnode:partition(), node(),
                                      riak_core_vnode:state()) -> vn_next().
'riak_core_vnode:start_handoff'(_, _, _, _) -> error(overlay).

%% the options are for riak_core_handoff_manager:add_outbound/7, the size is the one that the callback
%% is_empty/1 of the vnode module gives
-spec 'riak_core_vnode:start_outbound'(riak_core_handoff_manager:ho_type(), riak_core_vnode:partition(), node(),
                                       [{size, pos_integer()}], riak_core_vnode:state()) ->
          riak_core_vnode:state().
'riak_core_vnode:start_outbound'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_vnode:start_manager_event_timer'(vn_manager_event(), riak_core_vnode:state()) ->
          riak_core_vnode:state().
'riak_core_vnode:start_manager_event_timer'(_, _) -> error(overlay).

-spec 'riak_core_vnode:stop_manager_event_timer'(riak_core_vnode:state()) -> ok.
'riak_core_vnode:stop_manager_event_timer'(_) -> error(overlay).

%% tells the vnode module about the forwarding, if it exports set_vnode_forwarding/2
-spec 'riak_core_vnode:mod_set_forwarding'(vn_forward(), riak_core_vnode:state()) -> riak_core_vnode:state().
'riak_core_vnode:mod_set_forwarding'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_worker
%% ---------------------------------------------------------------------------------------------

%% the record state as a tuple
-type vw_state() :: {state, atom(), riak_core_vnode_worker:mod_state()}.

%% poolboy starts the worker with the arguments of poolboy:start_link/1 in riak_core_vnode_worker_pool:init/1,
%% a property list. Read are worker_callback_mod and worker_args.
-spec 'riak_core_vnode_worker:start_link'([{atom(), term()}]) -> {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_worker:start_link'(_) -> error(overlay).

%% the work is what the callback handle_work/3 of the worker module gets
-spec 'riak_core_vnode_worker:handle_work'(pid(), term(), riak_core_vnode_worker:sender()) -> ok.
'riak_core_vnode_worker:handle_work'(_, _, _) -> error(overlay).

%% the fourth argument is the pool, it gets the worker back with checkin_worker/2
-spec 'riak_core_vnode_worker:handle_work'(pid(), term(), riak_core_vnode_worker:sender(), pid()) -> ok.
'riak_core_vnode_worker:handle_work'(_, _, _, _) -> error(overlay).

%% [Module, VNodeIndex, WorkerArgs, WorkerProps, Caller]: the worker arguments are any term (callback
%% init_worker/3), so nothing more can be said about the elements
-spec 'riak_core_vnode_worker:init'([term()]) -> {ok, vw_state()}.
'riak_core_vnode_worker:init'(_) -> error(overlay).

-spec 'riak_core_vnode_worker:handle_call'(term(), {pid(), term()}, vw_state()) -> {reply, ok, vw_state()}.
'riak_core_vnode_worker:handle_call'(_, _, _) -> error(overlay).

%% {work, Work, WorkFrom, Caller} of handle_work/4, every other cast is ignored
-spec 'riak_core_vnode_worker:handle_cast'(term(), vw_state()) -> {noreply, vw_state()}.
'riak_core_vnode_worker:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker:handle_info'(term(), vw_state()) -> {noreply, vw_state()}.
'riak_core_vnode_worker:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker:terminate'(term(), vw_state()) -> ok.
'riak_core_vnode_worker:terminate'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker:code_change'(term(), vw_state(), term()) -> {ok, vw_state()}.
'riak_core_vnode_worker:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_worker_pool
%% ---------------------------------------------------------------------------------------------

%% the record state as a tuple
-type wp_state() :: {state, queue:queue() | list(), pid(), list(), fifo | filo, undefined | {pid(), reference()}}.
%% the names of the states of the gen_statem
-type wp_state_name() :: ready | queue | shutdown.
%% work as it waits in the queue: the cast of handle_work/3
-type wp_work() :: {work, term(), riak_core_vnode:sender()}.
%% the field queue: a queue for the strategy fifo, a stack for filo
-type wp_queue() :: queue:queue(wp_work()) | [wp_work()].
%% the field monitors: per busy worker its monitor, the sender and the work
-type wp_monitors() :: [{pid(), reference(), riak_core_vnode:sender(), term()}].
%% the casts, and the message of the monitor of a worker
-type wp_cast() :: wp_work() | worker_start | {checkin, pid()}.
-type wp_down() :: {'DOWN', reference(), process, pid(), term()}.
%% the From of a gen_statem call. The field shutdown, which keeps it, says {pid(), reference()}.
-type wp_from() :: {pid(), term()}.
%% what a cast leads to: the next state is ready or queue, or stays shutdown (see worker_started/2)
-type wp_next() :: {next_state, wp_state_name(), wp_state()}.
%% the call of shutdown_pool/2 in the states ready and queue: the state timeout forces the shutdown
-type wp_to_shutdown() :: {next_state, shutdown, wp_state(), [{state_timeout, integer(), force_shutdown}]}.

%% the worker arguments and properties are for the callback init_worker/3 of the worker module:
%% Args :: term(), Props :: [{atom(), term()}]
-spec 'riak_core_vnode_worker_pool:start_link'(module(), pos_integer(), riak_core_vnode:partition(), term(),
                                               [{atom(), term()}]) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_worker_pool:start_link'(_, _, _, _, _) -> error(overlay).

%% the only option that init/1 reads is the strategy of the queue
-spec 'riak_core_vnode_worker_pool:start_link'(module(), pos_integer(), riak_core_vnode:partition(), term(),
                                               [{atom(), term()}], [{strategy, fifo | filo}]) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_worker_pool:start_link'(_, _, _, _, _, _) -> error(overlay).

%% the work is for the callback handle_work/3 of the worker module (Work :: term())
-spec 'riak_core_vnode_worker_pool:handle_work'(pid(), term(), riak_core_vnode:sender()) -> ok.
'riak_core_vnode_worker_pool:handle_work'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:worker_started'(pid()) -> ok.
'riak_core_vnode_worker_pool:worker_started'(_) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:checkin_worker'(pid(), pid()) -> ok.
'riak_core_vnode_worker_pool:checkin_worker'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:stop'(pid(), term()) -> ok.
'riak_core_vnode_worker_pool:stop'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:callback_mode'() -> [state_functions | state_enter].
'riak_core_vnode_worker_pool:callback_mode'() -> error(overlay).

%% [WorkerMod, PoolSize, VNodeIndex, WorkerArgs, WorkerProps, Opts]: the worker arguments are any term, so
%% nothing more can be said about the elements
-spec 'riak_core_vnode_worker_pool:init'([term()]) -> {ok, ready, wp_state()}.
'riak_core_vnode_worker_pool:init'(_) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:terminate'(term(), wp_state_name(), wp_state()) -> ok.
'riak_core_vnode_worker_pool:terminate'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:code_change'(term(), wp_state_name(), wp_state(), term()) ->
          {ok, wp_state_name(), wp_state()}.
'riak_core_vnode_worker_pool:code_change'(_, _, _, _) -> error(overlay).

%% A state function (callback mode state_functions with state_enter) is one function per type of event and
%% gen_statem calls it with matching pairs only, hence the overloaded spec. The content is the state before
%% for enter, a cast, {shutdown, Wait} for the call of shutdown_pool/2, the 'DOWN' of a worker for info;
%% no clause takes anything else.
-spec 'riak_core_vnode_worker_pool:ready'
        (enter, wp_state_name(), wp_state()) -> {keep_state, wp_state()};
        (cast, wp_cast(), wp_state()) -> wp_next();
        ({call, wp_from()}, {shutdown, integer()}, wp_state()) -> wp_to_shutdown();
        (info, wp_down(), wp_state()) -> {keep_state, wp_state()}.
'riak_core_vnode_worker_pool:ready'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:queue'
        (enter, wp_state_name(), wp_state()) -> {keep_state, wp_state()};
        (cast, wp_cast(), wp_state()) -> wp_next();
        ({call, wp_from()}, {shutdown, integer()}, wp_state()) -> wp_to_shutdown();
        (info, wp_down(), wp_state()) -> {keep_state, wp_state()}.
'riak_core_vnode_worker_pool:queue'(_, _, _) -> error(overlay).

%% as ready/3, and the state timeout that the call of shutdown_pool/2 has set. The caller of shutdown_pool/2
%% gets ok when the last busy worker is back (at once if none is busy) or the error after the timeout;
%% who calls in between gets the error at once.
-spec 'riak_core_vnode_worker_pool:shutdown'
        (enter, wp_state_name(), wp_state()) ->
          {keep_state, wp_state()} | {stop_and_reply, shutdown, [{reply, wp_from(), ok}]};
        (state_timeout, force_shutdown, wp_state()) ->
          {stop_and_reply, shutdown, [{reply, wp_from(), {error, vnode_shutdown}}]};
        (cast, wp_cast(), wp_state()) ->
          {keep_state, wp_state()} | wp_next() | {stop_and_reply, shutdown, [{reply, wp_from(), ok}]};
        ({call, wp_from()}, {shutdown, integer()}, wp_state()) ->
          {keep_state, wp_state(), [{reply, wp_from(), {error, vnode_shutdown}}]};
        (info, wp_down(), wp_state()) -> {keep_state, wp_state()}.
'riak_core_vnode_worker_pool:shutdown'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:monitor_worker'(pid(), riak_core_vnode:sender(), term(), wp_monitors()) ->
          wp_monitors().
'riak_core_vnode_worker_pool:monitor_worker'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:demonitor_worker'(pid(), wp_monitors()) -> wp_monitors().
'riak_core_vnode_worker_pool:demonitor_worker'(_, _) -> error(overlay).

%% every sender of queued work gets {error, vnode_shutdown}
-spec 'riak_core_vnode_worker_pool:discard_queued_work'(wp_state()) -> ok.
'riak_core_vnode_worker_pool:discard_queued_work'(_) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:in'(wp_work(), wp_state()) -> wp_state().
'riak_core_vnode_worker_pool:in'(_, _) -> error(overlay).

%% the result of queue:out/1 for both strategies
-spec 'riak_core_vnode_worker_pool:out'(wp_state()) -> {{value, wp_work()}, wp_queue()} | {empty, wp_queue()}.
'riak_core_vnode_worker_pool:out'(_) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:new'(wp_state()) -> wp_queue().
'riak_core_vnode_worker_pool:new'(_) -> error(overlay).

%% the second argument is the state the pool is in: queue with an empty queue becomes ready
-spec 'riak_core_vnode_worker_pool:worker_started'(wp_state(), wp_state_name()) -> wp_next().
'riak_core_vnode_worker_pool:worker_started'(_, _) -> error(overlay).

-spec 'riak_core_vnode_worker_pool:checkin'(wp_state(), pid()) -> {next_state, queue | ready, wp_state()}.
'riak_core_vnode_worker_pool:checkin'(_, _) -> error(overlay).

%% the third argument is the exit reason of the worker
-spec 'riak_core_vnode_worker_pool:exit_worker'(wp_state(), pid(), term()) -> {ok, wp_state()}.
'riak_core_vnode_worker_pool:exit_worker'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_manager
%% ---------------------------------------------------------------------------------------------

%% The index of a vnode is written partition() throughout, as in repair/3. index() of
%% riak_core_handoff.hrl is the same type and comes in through mod_partition() and known_handoff().
%% The owner of an index is a node(), as in repair_pairs/2 and #repair{}; riak_core_ring says term().

%% #state{}. idxtab has no declared type: it is the table that find_vnodes/1 creates.
-type vm_state() :: {state, ets:tab(), dict:dict(), dict:dict(), [term()], [{integer(), term()}], integer(),
                     term(), riak_core_vnode_manager:repairs()}.

%% #idxrec{} and #monrec{}, the rows of the table; none of their fields has a declared type
-type vm_idxrec() :: {idxrec, {riak_core_vnode_manager:partition(), module()},
                      riak_core_vnode_manager:partition(), module(), pid(), reference()}.
-type vm_monrec() :: {monrec, reference(), {riak_core_vnode_manager:partition(), module()}}.

%% a running vnode
-type vm_vnode() :: {module(), riak_core_vnode_manager:partition(), pid()}.

%% chashbin:chashbin(), which this module only hands on (should_handoff/4 ignores it) and never names.
%% The last field is erlang:tuple(node()) in chashbin.erl.
-type vm_chashbin() :: {chashbin, pos_integer(), <<_:_*176>>, tuple()}.

%% riak_core_ring_manager:get_ring_id/0: epoch and counter. The field last_ring_id says term().
-type vm_ring_id() :: {non_neg_integer(), non_neg_integer()}.

%% an entry of riak_core_ring:pending_changes/1: index, owner, next owner (a node, '$resize' or
%% '$delete'), the modules that are done, status. The two owners are term() in the field next of
%% #chstate{}; this module only compares the owner with node().
-type vm_transfer() :: {riak_core_vnode_manager:partition(), term(), term(), [module()], awaiting | complete}.

%% the target of a handoff as in known_handoff(): a node or an action of a resize
-type vm_target() :: node() | '$resize' | '$delete'.

%% the result of riak_core_ring:vnode_type/2, with the owner as a node
-type vm_vnode_type() :: primary | {fallback, node()} | future_primary | resized_primary.

%% where a vnode forwards its requests to: nowhere, the next owner, or the targets of the completed
%% resize transfers. The field forward of the state of riak_core_vnode has the last two.
-type vm_forward() :: undefined | node() | [{riak_core_vnode_manager:partition(), node()}].

%% the dict in the field forwarding of the state (declared as dict:dict())
-type vm_forwarding() :: dict:dict(riak_core_vnode_manager:mod_partition(), vm_forward()).

%% all_vnodes_status/0: a vnode has a single property, or a list as soon as two sources know it
-type vm_status_prop() :: {type, primary | secondary} | {pid, pid()}
                        | {forwarding, node() | [{riak_core_vnode_manager:partition(), node()}]}
                        | {should_handoff, vm_target()}.
-type vm_vnode_status() :: {riak_core_vnode_manager:mod_partition(), vm_status_prop() | [vm_status_prop()]}.

%% the result of repair/3
-type vm_repair_reply() :: {ok, [{riak_core_vnode_manager:partition(), node()}]}
                         | {down, [{riak_core_vnode_manager:partition(), node()}]}
                         | ownership_change_in_progress.

%% the replies of handle_call/3 in the order of its clauses; ok is also the reply to an unknown request
-type vm_reply() :: [vm_vnode_status()]
                  | [vm_vnode()]
                  | [{riak_core_vnode_manager:partition(), pid()}]
                  | {ok, pid() | [pid()]}
                  | [vm_idxrec() | vm_monrec()]
                  | vm_repair_reply()
                  | [riak_core_vnode_manager:known_handoff()]
                  | not_found | in_progress
                  | ok.

-spec 'riak_core_vnode_manager:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_manager:start_link'() -> error(overlay).

%% handle_cast/2 has no clause for stop, the server ignores it
-spec 'riak_core_vnode_manager:stop'() -> ok.
'riak_core_vnode_manager:stop'() -> error(overlay).

-spec 'riak_core_vnode_manager:all_vnodes_status'() -> [vm_vnode_status()].
'riak_core_vnode_manager:all_vnodes_status'() -> error(overlay).

%% the reason is only logged and handed on to riak_core_handoff_manager:kill_xfer/3
-spec 'riak_core_vnode_manager:kill_repairs'(term()) -> ok.
'riak_core_vnode_manager:kill_repairs'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:force_handoffs'() -> ok.
'riak_core_vnode_manager:force_handoffs'() -> error(overlay).

-spec 'riak_core_vnode_manager:unregister_vnode'(riak_core_vnode_manager:partition(), module()) -> ok.
'riak_core_vnode_manager:unregister_vnode'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:unregister_vnode'(riak_core_vnode_manager:partition(), pid(), module()) -> ok.
'riak_core_vnode_manager:unregister_vnode'(_, _, _) -> error(overlay).

%% a list of indices starts them all, see get_vnode/3
-spec 'riak_core_vnode_manager:start_vnode'(riak_core_vnode_manager:partition() |
                                            [riak_core_vnode_manager:partition()], module()) -> ok.
'riak_core_vnode_manager:start_vnode'(_, _) -> error(overlay).

%% the events that handle_vnode_event/5 knows; riak_core_vnode sends exactly these
-spec 'riak_core_vnode_manager:vnode_event'(module(), riak_core_vnode_manager:partition(), pid(),
                                            inactive | handoff_complete | handoff_error) -> ok.
'riak_core_vnode_manager:vnode_event'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:get_tab'() -> [vm_idxrec() | vm_monrec()].
'riak_core_vnode_manager:get_tab'() -> error(overlay).

%% starts the vnode if it does not run. The callers in riak_core pass one index and use the result as
%% a pid; a list comes from the start_vnodes/1 of a vnode module (riak_core_vnode_master:get_vnode_pid/2).
-spec 'riak_core_vnode_manager:get_vnode_pid'(riak_core_vnode_manager:partition(), module()) -> {ok, pid()};
                                             ([riak_core_vnode_manager:partition()], module()) -> {ok, [pid()]}.
'riak_core_vnode_manager:get_vnode_pid'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:all_vnodes'() -> [vm_vnode()].
'riak_core_vnode_manager:all_vnodes'() -> error(overlay).

%% get_all_vnodes/1 also takes a list of modules, the API is meant for one
-spec 'riak_core_vnode_manager:all_vnodes'(module()) -> [vm_vnode()].
'riak_core_vnode_manager:all_vnodes'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:all_index_pid'(module()) -> [{riak_core_vnode_manager:partition(), pid()}].
'riak_core_vnode_manager:all_index_pid'(_) -> error(overlay).

%% the second argument is the result if the table cannot be read: ets_error or []
-spec 'riak_core_vnode_manager:get_all_index_pid'(module(), Default) ->
          [{riak_core_vnode_manager:partition(), pid()}] | Default.
'riak_core_vnode_manager:get_all_index_pid'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:get_all_vnodes'() -> [vm_vnode()].
'riak_core_vnode_manager:get_all_vnodes'() -> error(overlay).

-spec 'riak_core_vnode_manager:get_all_vnodes'(module() | [module()]) -> [vm_vnode()].
'riak_core_vnode_manager:get_all_vnodes'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:init'([]) -> {ok, vm_state()}.
'riak_core_vnode_manager:init'(_) -> error(overlay).

%% the state comes without a table (idxtab is undefined) and leaves with it
-spec 'riak_core_vnode_manager:find_vnodes'(vm_state()) -> vm_state().
'riak_core_vnode_manager:find_vnodes'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:handle_call'(term(), {pid(), term()}, vm_state()) ->
          {reply, vm_reply(), vm_state()}.
'riak_core_vnode_manager:handle_call'(_, _, _) -> error(overlay).

%% every element is {{Mod, SrcIdx}, {repair, inbound, Node}}
-spec 'riak_core_vnode_manager:transform_repair_records'(riak_core_vnode_manager:repairs()) ->
          [riak_core_vnode_manager:known_handoff()].
'riak_core_vnode_manager:transform_repair_records'(_) -> error(overlay).

%% the service is the first argument of repair/3
-spec 'riak_core_vnode_manager:maybe_create_repair'(riak_core_vnode_manager:partition(), atom(),
                                                    riak_core_vnode_manager:mod_partition(), {module(), atom()},
                                                    module(), riak_core_vnode_manager:repairs(), vm_state()) ->
          {reply, vm_repair_reply(), vm_state()}.
'riak_core_vnode_manager:maybe_create_repair'(_, _, _, _, _, _, _) -> error(overlay).

%% the pairs are the three of repair_pairs/2
-spec 'riak_core_vnode_manager:create_repair'([{riak_core_vnode_manager:partition(), node()}],
                                              riak_core_vnode_manager:mod_partition(), {module(), atom()},
                                              module(), riak_core_vnode_manager:partition(),
                                              riak_core_vnode_manager:repairs(), vm_state()) ->
          {reply, {ok, [{riak_core_vnode_manager:partition(), node()}]}, vm_state()}.
'riak_core_vnode_manager:create_repair'(_, _, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:handle_cast'(term(), vm_state()) -> {noreply, vm_state()}.
'riak_core_vnode_manager:handle_cast'(_, _) -> error(overlay).

%% no catch-all clause. The monitors are all on pids.
-spec 'riak_core_vnode_manager:handle_info'(management_tick | {'DOWN', reference(), process, pid(), term()},
                                            vm_state()) -> {noreply, vm_state()}.
'riak_core_vnode_manager:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:handle_vnode_event'(inactive | handoff_complete | handoff_error, module(),
                                                   riak_core_vnode_manager:partition(), pid(), vm_state()) ->
          {noreply, vm_state()}.
'riak_core_vnode_manager:handle_vnode_event'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:terminate'(term(), vm_state()) -> ok.
'riak_core_vnode_manager:terminate'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:code_change'(term(), vm_state(), term()) -> {ok, vm_state()}.
'riak_core_vnode_manager:code_change'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_ring_changed'(vm_ring_id(), riak_core_ring:riak_core_ring(), vm_chashbin(),
                                                   vm_state()) -> vm_state().
'riak_core_vnode_manager:maybe_ring_changed'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:ring_changed'(riak_core_ring:riak_core_ring(), vm_chashbin(), vm_state()) ->
          vm_state().
'riak_core_vnode_manager:ring_changed'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_ensure_vnodes_started'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_vnode_manager:maybe_ensure_vnodes_started'(_) -> error(overlay).

%% the process that runs riak_core_ring_handler:ensure_vnodes_started/1
-spec 'riak_core_vnode_manager:ensure_vnodes_started'(riak_core_ring:riak_core_ring()) -> pid().
'riak_core_vnode_manager:ensure_vnodes_started'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:schedule_management_timer'() -> reference().
'riak_core_vnode_manager:schedule_management_timer'() -> error(overlay).

-spec 'riak_core_vnode_manager:trigger_ownership_handoff'([vm_transfer()], [module()],
                                                          riak_core_ring:riak_core_ring(), vm_state()) -> ok.
'riak_core_vnode_manager:trigger_ownership_handoff'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:limit_ownership_handoff'([vm_transfer()], boolean()) -> [vm_transfer()].
'riak_core_vnode_manager:limit_ownership_handoff'(_, _) -> error(overlay).

%% the limit is the length of a lists:sublist/2
-spec 'riak_core_vnode_manager:limit_ownership_handoff'(non_neg_integer(), [vm_transfer()], boolean()) ->
          [vm_transfer()].
'riak_core_vnode_manager:limit_ownership_handoff'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:idx2vnode'(riak_core_vnode_manager:partition(), module(), vm_state()) ->
          pid() | no_match.
'riak_core_vnode_manager:idx2vnode'(_, _, _) -> error(overlay).

%% the result of ets:delete/2 or ets:match_delete/2
-spec 'riak_core_vnode_manager:delmon'(reference(), vm_state()) -> true.
'riak_core_vnode_manager:delmon'(_, _) -> error(overlay).

%% get_vnode/3 inserts the two records of a vnode at once
-spec 'riak_core_vnode_manager:add_vnode_rec'([vm_idxrec() | vm_monrec()], vm_state()) -> true.
'riak_core_vnode_manager:add_vnode_rec'(_, _) -> error(overlay).

%% two functions in one (first clause: when not is_list(Idx)); maybe_trigger_handoff/3 and the reply
%% to get_vnode rely on the pid for one index
-spec 'riak_core_vnode_manager:get_vnode'(riak_core_vnode_manager:partition(), module(), vm_state()) -> pid();
                                         ([riak_core_vnode_manager:partition()], module(), vm_state()) -> [pid()].
'riak_core_vnode_manager:get_vnode'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:get_forward'(module(), riak_core_vnode_manager:partition(), vm_state()) ->
          vm_forward().
'riak_core_vnode_manager:get_forward'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:check_forward'(riak_core_ring:riak_core_ring(), module(),
                                              riak_core_vnode_manager:partition()) ->
          {riak_core_vnode_manager:mod_partition(), vm_forward()}.
'riak_core_vnode_manager:check_forward'(_, _, _) -> error(overlay).

%% the dict has the next owner of the completed transfers of this node, the fourth argument is the
%% owner of the index
-spec 'riak_core_vnode_manager:check_forward_precomputed'(dict:dict(riak_core_vnode_manager:mod_partition(),
                                                                    vm_target()),
                                                          module(), riak_core_vnode_manager:partition(), node(),
                                                          riak_core_ring:riak_core_ring()) ->
          {riak_core_vnode_manager:mod_partition(), vm_forward()}.
'riak_core_vnode_manager:check_forward_precomputed'(_, _, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:compute_forwarding'([module()], riak_core_ring:riak_core_ring()) ->
          vm_forwarding().
'riak_core_vnode_manager:compute_forwarding'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:update_forwarding'([vm_vnode()], [module()], riak_core_ring:riak_core_ring(),
                                                  vm_state()) -> vm_state().
'riak_core_vnode_manager:update_forwarding'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:update_forwarding'(riak_core_vnode_manager:mod_partition(),
                                                  riak_core_ring:riak_core_ring(), vm_state()) -> vm_state().
'riak_core_vnode_manager:update_forwarding'(_, _, _) -> error(overlay).

%% the dict has the pids of the running vnodes
-spec 'riak_core_vnode_manager:change_forward'(dict:dict(riak_core_vnode_manager:mod_partition(), pid()),
                                               module(), riak_core_vnode_manager:partition(), vm_forward()) -> ok.
'riak_core_vnode_manager:change_forward'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:update_handoff'([vm_vnode()], riak_core_ring:riak_core_ring(), vm_chashbin(),
                                               vm_state()) -> vm_state().
'riak_core_vnode_manager:update_handoff'(_, _, _, _) -> error(overlay).

%% a target node is only found for a primary or a fallback, see determine_handoff_target/5 and the case
%% in update_handoff/4
-spec 'riak_core_vnode_manager:should_handoff'(riak_core_ring:riak_core_ring(), vm_chashbin(), module(),
                                               riak_core_vnode_manager:partition()) ->
          false | {true, '$resize' | '$delete'} | {true, primary | {fallback, node()}, node()}.
'riak_core_vnode_manager:should_handoff'(_, _, _, _) -> error(overlay).

%% the second argument is the next owner of riak_core_ring:next_owner/2
-spec 'riak_core_vnode_manager:determine_handoff_target'(vm_vnode_type(), undefined | vm_target(), boolean(),
                                                         boolean()) -> undefined | vm_target().
'riak_core_vnode_manager:determine_handoff_target'(_, _, _, _) -> error(overlay).

%% the last argument: this node is the next owner
-spec 'riak_core_vnode_manager:determine_handoff_target'(vm_vnode_type(), undefined | vm_target(), boolean(),
                                                         boolean(), boolean()) -> undefined | vm_target().
'riak_core_vnode_manager:determine_handoff_target'(_, _, _, _, _) -> error(overlay).

%% the application that registered the vnode module
-spec 'riak_core_vnode_manager:app_for_vnode_module'(module()) -> {ok, atom()} | undefined.
'riak_core_vnode_manager:app_for_vnode_module'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_trigger_handoff'(module(), riak_core_vnode_manager:partition(),
                                                      vm_state()) -> ok.
'riak_core_vnode_manager:maybe_trigger_handoff'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_trigger_handoff'(module(), riak_core_vnode_manager:partition(), pid(),
                                                      vm_state()) -> ok.
'riak_core_vnode_manager:maybe_trigger_handoff'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:get_all_vnodes_status'(vm_state()) -> [vm_vnode_status()].
'riak_core_vnode_manager:get_all_vnodes_status'(_) -> error(overlay).

-spec 'riak_core_vnode_manager:update_never_started'(riak_core_ring:riak_core_ring(), vm_state()) -> vm_state().
'riak_core_vnode_manager:update_never_started'(_, _) -> error(overlay).

%% the indices are all those of the ring
-spec 'riak_core_vnode_manager:update_never_started'(module(), [riak_core_vnode_manager:partition()],
                                                     vm_state()) -> vm_state().
'riak_core_vnode_manager:update_never_started'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_start_vnodes'(riak_core_ring:riak_core_ring(), vm_state()) -> vm_state().
'riak_core_vnode_manager:maybe_start_vnodes'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:maybe_start_vnodes'(vm_state()) -> vm_state().
'riak_core_vnode_manager:maybe_start_vnodes'(_) -> error(overlay).

%% the reason as in kill_repairs/2
-spec 'riak_core_vnode_manager:kill_repair'(riak_core_vnode_manager:repair(), term()) -> ok.
'riak_core_vnode_manager:kill_repair'(_, _) -> error(overlay).

-spec 'riak_core_vnode_manager:register_vnode_stats'(module(), riak_core_vnode_manager:partition(), pid()) -> ok.
'riak_core_vnode_manager:register_vnode_stats'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_manager:unregister_vnode_stats'(module(), riak_core_vnode_manager:partition()) -> ok.
'riak_core_vnode_manager:unregister_vnode_stats'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_sup
%% ---------------------------------------------------------------------------------------------

%% chash:index_as_int(); neither of the two supervisors names chash
-type sup_index() :: integer().

%% the arguments of riak_core_vnode:start_link/3; the third is what riak_core_vnode_manager:get_forward/3
%% finds. The result is the one of supervisor:start_child/2.
-spec 'riak_core_vnode_sup:start_vnode'(module(), sup_index(), undefined | node() | [{sup_index(), node()}]) ->
          supervisor:startchild_ret().
'riak_core_vnode_sup:start_vnode'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_sup:start_link'() -> error(overlay).

-spec 'riak_core_vnode_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_vnode_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_proxy_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_vnode_proxy_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_proxy_sup:start_link'() -> error(overlay).

-spec 'riak_core_vnode_proxy_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_vnode_proxy_sup:init'(_) -> error(overlay).

%% the pid of the proxy, started now or before
-spec 'riak_core_vnode_proxy_sup:start_proxy'(module(), sup_index()) -> pid().
'riak_core_vnode_proxy_sup:start_proxy'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy_sup:stop_proxy'(module(), sup_index()) -> ok.
'riak_core_vnode_proxy_sup:stop_proxy'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy_sup:start_proxies'(module()) -> ok.
'riak_core_vnode_proxy_sup:start_proxies'(_) -> error(overlay).

-spec 'riak_core_vnode_proxy_sup:proxy_ref'(module(), sup_index()) -> supervisor:child_spec().
'riak_core_vnode_proxy_sup:proxy_ref'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy_sup:get_indices'() -> [sup_index()].
'riak_core_vnode_proxy_sup:get_indices'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_master
%% ---------------------------------------------------------------------------------------------

%% -record(state, {idxtab, sup_name, vnode_mod, legacy}): no field has a type. idxtab is only ever set
%% to undefined and sup_name is never set; legacy is the module with rewrite_cast/1 and rewrite_call/2.
-type vmaster_state() :: {state, undefined, undefined, module(), module() | undefined}.

%% one destination of a command: a partition with the node that owns it or with the pid of its vnode
-type vmaster_dest() :: {riak_core_vnode_master:partition(), node() | pid()}.

%% a preflist, or a single destination: command2/5 makes a list of it
-type vmaster_dests() :: [vmaster_dest()] | vmaster_dest().

%% the two requests that a master forwards to a vnode proxy
-type vmaster_req() :: riak_core_vnode_master:riak_vnode_req_v1() |
                       riak_core_vnode_master:riak_coverage_req_v1().

%% normal: gen_fsm_compat:send_event/2, unreliable: riak_core_send_msg:send_event_unreliable/2
-type vmaster_how() :: normal | unreliable.

-spec 'riak_core_vnode_master:make_name'(module(), string()) -> atom().
'riak_core_vnode_master:make_name'(_, _) -> error(overlay).

%% the registered name of the master of a vnode module; this is the VMaster of the functions below
-spec 'riak_core_vnode_master:reg_name'(module()) -> atom().
'riak_core_vnode_master:reg_name'(_) -> error(overlay).

-spec 'riak_core_vnode_master:vmaster_to_vmod'(atom()) -> module().
'riak_core_vnode_master:vmaster_to_vmod'(_) -> error(overlay).

-spec 'riak_core_vnode_master:start_link'(module()) -> {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_master:start_link'(_) -> error(overlay).

%% the second argument is the legacy module, undefined for none
-spec 'riak_core_vnode_master:start_link'(module(), module() | undefined) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_master:start_link'(_, _) -> error(overlay).

%% the third argument is the service (riak_core_node_watcher:service_up/2,3,4 says Id :: atom()) that the
%% master waits for, undefined for none
-spec 'riak_core_vnode_master:start_link'(module(), module() | undefined, atom()) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_vnode_master:start_link'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:start_vnode'(riak_core_vnode_master:partition(), module()) -> ok.
'riak_core_vnode_master:start_vnode'(_, _) -> error(overlay).

%% the reply of riak_core_vnode_manager to {Index, VNodeMod, get_vnode}
-spec 'riak_core_vnode_master:get_vnode_pid'(riak_core_vnode_master:partition(), module()) -> {ok, pid()}.
'riak_core_vnode_master:get_vnode_pid'(_, _) -> error(overlay).

%% command2/5 takes a preflist or a single destination, so all four entry points do; the last argument
%% is the registered name of the master (reg_name/1)
-spec 'riak_core_vnode_master:command'(vmaster_dests(), riak_core_vnode_master:vnode_req(), atom()) -> ok.
'riak_core_vnode_master:command'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:command_unreliable'(vmaster_dests(), riak_core_vnode_master:vnode_req(), atom()) ->
          ok.
'riak_core_vnode_master:command_unreliable'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:command'(vmaster_dests(), riak_core_vnode_master:vnode_req(),
                                       riak_core_vnode_master:sender(), atom()) -> ok.
'riak_core_vnode_master:command'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:command_unreliable'(vmaster_dests(), riak_core_vnode_master:vnode_req(),
                                                  riak_core_vnode_master:sender(), atom()) -> ok.
'riak_core_vnode_master:command_unreliable'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:command2'(vmaster_dests(), riak_core_vnode_master:vnode_req(),
                                        riak_core_vnode_master:sender(), atom(), vmaster_how()) -> ok.
'riak_core_vnode_master:command2'(_, _, _, _, _) -> error(overlay).

%% a list of vnodes gives a list of ok (and wants a sender that is a triple), a single vnode gives ok;
%% the only caller (riak_core_vnode) passes a single vnode and ignores the result, so a union and no
%% overloaded spec
-spec 'riak_core_vnode_master:coverage'(riak_core_vnode_master:vnode_req(),
                                        [{riak_core_vnode_master:partition(), node()}] |
                                        {riak_core_vnode_master:partition(), node()},
                                        riak_core_vnode_master:keyspaces(), riak_core_vnode_master:sender(),
                                        atom()) -> ok | [ok].
'riak_core_vnode_master:coverage'(_, _, _, _, _) -> error(overlay).

%% the result is the one of riak_core_vnode_proxy:command_return_vnode/2
-spec 'riak_core_vnode_master:command_return_vnode'({riak_core_vnode_master:partition(), node()},
                                                    riak_core_vnode_master:vnode_req(),
                                                    riak_core_vnode_master:sender(), atom()) ->
          {ok, pid()} | {error, term()}.
'riak_core_vnode_master:command_return_vnode'(_, _, _, _) -> error(overlay).

%% the result is the reply of the vnode module to the request; {vnode_error, _} is raised as an error
-spec 'riak_core_vnode_master:sync_command'({riak_core_vnode_master:partition(), node()},
                                            riak_core_vnode_master:vnode_req(), atom()) -> term().
'riak_core_vnode_master:sync_command'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:sync_command'({riak_core_vnode_master:partition(), node()},
                                            riak_core_vnode_master:vnode_req(), atom(), timeout()) -> term().
'riak_core_vnode_master:sync_command'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:sync_spawn_command'({riak_core_vnode_master:partition(), node()},
                                                  riak_core_vnode_master:vnode_req(), atom()) -> term().
'riak_core_vnode_master:sync_spawn_command'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:all_nodes'(module()) -> [pid()].
'riak_core_vnode_master:all_nodes'(_) -> error(overlay).

%% [Service, VNodeMod, LegacyMod, RegName] of start_link/3
-spec 'riak_core_vnode_master:init'([atom(), ...]) -> {ok, vmaster_state()}.
'riak_core_vnode_master:init'(_) -> error(overlay).

%% the first argument is the master on a node
-spec 'riak_core_vnode_master:proxy_cast'({atom(), node()}, vmaster_req()) -> ok.
'riak_core_vnode_master:proxy_cast'(_, _) -> error(overlay).

-spec 'riak_core_vnode_master:proxy_cast'({atom(), node()}, vmaster_req(), vmaster_how()) -> ok.
'riak_core_vnode_master:proxy_cast'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:do_proxy_cast'({atom(), node()}, vmaster_req(), vmaster_how()) -> ok.
'riak_core_vnode_master:do_proxy_cast'(_, _, _) -> error(overlay).

%% the destination is the result of riak_core_vnode_proxy:reg_name/3
-spec 'riak_core_vnode_master:send_an_event'({atom(), node()}, vmaster_req(), vmaster_how()) -> ok.
'riak_core_vnode_master:send_an_event'(_, _, _) -> error(overlay).

%% the last clause takes any message (for Legacy:rewrite_cast/1), but only in a master with a legacy module
-spec 'riak_core_vnode_master:handle_cast'(term(), vmaster_state()) -> {noreply, vmaster_state()}.
'riak_core_vnode_master:handle_cast'(_, _) -> error(overlay).

%% as handle_cast/2: any message, for Legacy:rewrite_call/2
-spec 'riak_core_vnode_master:handle_call'(term(), {pid(), term()}, vmaster_state()) ->
          {reply, {ok, pid()}, vmaster_state()} | {noreply, vmaster_state()}.
'riak_core_vnode_master:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_master:handle_info'(term(), vmaster_state()) -> {noreply, vmaster_state()}.
'riak_core_vnode_master:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_vnode_master:terminate'(term(), vmaster_state()) -> ok.
'riak_core_vnode_master:terminate'(_, _) -> error(overlay).

-spec 'riak_core_vnode_master:code_change'(term(), vmaster_state(), term()) -> {ok, vmaster_state()}.
'riak_core_vnode_master:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_vnode_proxy
%% ---------------------------------------------------------------------------------------------

%% -record(state, {mod, index, vnode_pid, vnode_mref, check_mailbox, check_threshold, check_counter,
%% check_interval, check_request_interval, check_request}) with the declared field types.
%% check_request is declared undefined | sent | ignore, but the code keeps the reference of
%% send_proxy_ping/2 in it.
-type vp_state() :: {state, atom(), riak_core_vnode_proxy:partition(), pid() | undefined,
                     reference() | undefined, non_neg_integer(), pos_integer() | undefined, non_neg_integer(),
                     pos_integer(), non_neg_integer(), undefined | sent | ignore}.

%% where call/2,3 and cast/2 send to: a proxy by pid, by its registered name or by its name on a node
-type vp_dest() :: pid() | atom() | {atom(), node()}.

-spec 'riak_core_vnode_proxy:reg_name'(module(), riak_core_vnode_proxy:partition()) -> atom().
'riak_core_vnode_proxy:reg_name'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:reg_name'(module(), riak_core_vnode_proxy:partition(), node()) ->
          {atom(), node()}.
'riak_core_vnode_proxy:reg_name'(_, _, _) -> error(overlay).

%% init/1 acknowledges with {ok, self()} and never fails before that; {error, _} if the process dies
-spec 'riak_core_vnode_proxy:start_link'(module(), riak_core_vnode_proxy:partition()) ->
          {ok, pid()} | {error, term()}.
'riak_core_vnode_proxy:start_link'(_, _) -> error(overlay).

%% [Parent, RegName, Mod, Index] of start_link/2; ends in loop/2
-spec 'riak_core_vnode_proxy:init'([pid() | atom() | riak_core_vnode_proxy:partition(), ...]) -> no_return().
'riak_core_vnode_proxy:init'(_) -> error(overlay).

-spec 'riak_core_vnode_proxy:unregister_vnode'(module(), riak_core_vnode_proxy:partition(), pid()) -> ok.
'riak_core_vnode_proxy:unregister_vnode'(_, _, _) -> error(overlay).

%% the reply of handle_call/3 to overloaded, or the error of call_reply/1 (as in the spec of
%% command_return_vnode/2)
-spec 'riak_core_vnode_proxy:overloaded'({module(), riak_core_vnode_proxy:partition(), node()} | pid()) ->
          boolean() | {error, term()}.
'riak_core_vnode_proxy:overloaded'(_) -> error(overlay).

%% the reply depends on the message and both callers rely on it (command_return_vnode/2 has a spec):
%% handle_call/3 answers {return_vnode, Req} with {ok, Pid} and overloaded with a boolean, call_reply/1
%% makes {error, Reason} of a failed call. The last clause is the spec of call_reply/1 for any other
%% message (the proxy answers it with ok); it overlaps the two before it.
-spec 'riak_core_vnode_proxy:call'(vp_dest(), {return_vnode, term()}) -> {ok, pid()} | {error, term()};
                                  (vp_dest(), overloaded) -> boolean() | {error, term()};
                                  (vp_dest(), term()) -> term().
'riak_core_vnode_proxy:call'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:call'(vp_dest(), {return_vnode, term()}, timeout()) -> {ok, pid()} | {error, term()};
                                  (vp_dest(), overloaded, timeout()) -> boolean() | {error, term()};
                                  (vp_dest(), term(), timeout()) -> term().
'riak_core_vnode_proxy:call'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:cast'(vp_dest(), term()) -> ok.
'riak_core_vnode_proxy:cast'(_, _) -> error(overlay).

%% the callbacks of sys:handle_system_msg/6: (Parent, Debug, Misc), the Misc of loop/2 is the state
-spec 'riak_core_vnode_proxy:system_continue'(pid(), [sys:dbg_opt()], vp_state()) -> no_return().
'riak_core_vnode_proxy:system_continue'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:system_terminate'(term(), pid(), [sys:dbg_opt()], vp_state()) -> no_return().
'riak_core_vnode_proxy:system_terminate'(_, _, _, _) -> error(overlay).

%% (Misc, Module, OldVsn, Extra)
-spec 'riak_core_vnode_proxy:system_code_change'(vp_state(), module(), term(), term()) -> {ok, vp_state()}.
'riak_core_vnode_proxy:system_code_change'(_, _, _, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:loop'(pid(), vp_state()) -> no_return().
'riak_core_vnode_proxy:loop'(_, _) -> error(overlay).

%% {return_vnode, Req}, overloaded, and ok for any other message
-spec 'riak_core_vnode_proxy:handle_call'(term(), {pid(), term()}, vp_state()) ->
          {reply, {ok, pid()} | boolean() | ok, vp_state()}.
'riak_core_vnode_proxy:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:handle_cast'(term(), vp_state()) -> {noreply, vp_state()}.
'riak_core_vnode_proxy:handle_cast'(_, _) -> error(overlay).

%% any other message of the mailbox, it goes to the vnode
-spec 'riak_core_vnode_proxy:handle_proxy'(term(), vp_state()) -> {noreply, vp_state()}.
'riak_core_vnode_proxy:handle_proxy'(_, _) -> error(overlay).

%% the result of `catch Mod:handle_overload_command/3' or `catch Mod:handle_overload_info/2'; nobody uses it
-spec 'riak_core_vnode_proxy:handle_overload'(term(), vp_state()) -> term().
'riak_core_vnode_proxy:handle_overload'(_, _) -> error(overlay).

-spec 'riak_core_vnode_proxy:forget_vnode'(vp_state()) -> vp_state().
'riak_core_vnode_proxy:forget_vnode'(_) -> error(overlay).

-spec 'riak_core_vnode_proxy:get_vnode_pid'(vp_state()) -> {pid(), vp_state()}.
'riak_core_vnode_proxy:get_vnode_pid'(_) -> error(overlay).

%% the second argument is the estimate of the mailbox of the vnode (check_mailbox)
-spec 'riak_core_vnode_proxy:send_proxy_ping'(pid(), non_neg_integer()) -> reference().
'riak_core_vnode_proxy:send_proxy_ping'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_listener
%% ---------------------------------------------------------------------------------------------

%% -record(state, {ipaddr :: string(), portnum :: integer()}).
-type hl_state() :: {state, string(), integer()}.

%% the result of gen_nb_server:start_link/4
-spec 'riak_core_handoff_listener:start_link'() -> {ok, pid()} | {error, term()}.
'riak_core_handoff_listener:start_link'() -> error(overlay).

-spec 'riak_core_handoff_listener:get_handoff_ip'() -> {ok, string()}.
'riak_core_handoff_listener:get_handoff_ip'() -> error(overlay).

%% [IpAddr, PortNum] of start_link/0
-spec 'riak_core_handoff_listener:init'([string() | integer(), ...]) -> {ok, hl_state()}.
'riak_core_handoff_listener:init'(_) -> error(overlay).

%% the type of the callback sock_opts/0 of gen_nb_server
-spec 'riak_core_handoff_listener:sock_opts'() -> [gen_tcp:listen_option()].
'riak_core_handoff_listener:sock_opts'() -> error(overlay).

-spec 'riak_core_handoff_listener:handle_call'(handoff_ip | handoff_port, {pid(), term()}, hl_state()) ->
          {reply, {ok, string()} | {ok, integer()}, hl_state()}.
'riak_core_handoff_listener:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_listener:handle_cast'(term(), hl_state()) -> {noreply, hl_state()}.
'riak_core_handoff_listener:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_handoff_listener:handle_info'(term(), hl_state()) -> {noreply, hl_state()}.
'riak_core_handoff_listener:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_handoff_listener:terminate'(term(), hl_state()) -> ok.
'riak_core_handoff_listener:terminate'(_, _) -> error(overlay).

-spec 'riak_core_handoff_listener:code_change'(term(), hl_state(), term()) -> {ok, hl_state()}.
'riak_core_handoff_listener:code_change'(_, _, _) -> error(overlay).

%% the callback new_connection/2 of gen_nb_server says inet:socket(); this module does not name inet,
%% gen_tcp:socket() is the same type
-spec 'riak_core_handoff_listener:new_connection'(gen_tcp:socket(), hl_state()) -> {ok, hl_state()}.
'riak_core_handoff_listener:new_connection'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% gen_nb_server
%% ---------------------------------------------------------------------------------------------

%% -record(state, {cb, sock, server_state}): no field has a type. cb is the callback module, sock the
%% listen socket (a port() in the @spec of listen_on/3), server_state the state of the callback module.
-type nb_state() :: {state, module(), port(), term()}.

%% inet:ip_address(), which the guard of listen_on/3 asks for (a tuple of size 4 or 8); gen_nb_server names
%% inet only in a -callback
-type nb_ip_address() :: {0..255, 0..255, 0..255, 0..255} |
                         {0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535, 0..65535}.

%% the result of a callback that may ask for a timeout or for hibernation
-type nb_noreply() :: {noreply, nb_state()} | {noreply, nb_state(), number() | hibernate} |
                      {stop, term(), nb_state()}.

%% the @spec: CallbackModule = atom(), IpAddr = string(), Port = integer(), InitParams = [any()],
%% Result = {ok, pid()} | {error, any()}
-spec 'gen_nb_server:start_link'(module(), string(), integer(), [any()]) -> {ok, pid()} | {error, any()}.
'gen_nb_server:start_link'(_, _, _, _) -> error(overlay).

%% [CallbackModule, IpAddr, Port, InitParams] of start_link/4; an error of CallbackModule:init/1 or of
%% listen_on/3 is the result
-spec 'gen_nb_server:init'([module() | string() | integer() | [any()], ...]) -> {ok, nb_state()} | {error, term()}.
'gen_nb_server:init'(_) -> error(overlay).

%% the results of the callback handle_call/3 with the state wrapped, and {stop, Reason, Reply, State}
-spec 'gen_nb_server:handle_call'(term(), {pid(), term()}, nb_state()) ->
          {reply, term(), nb_state()} | {reply, term(), nb_state(), number() | hibernate} |
          nb_noreply() | {stop, term(), term(), nb_state()}.
'gen_nb_server:handle_call'(_, _, _) -> error(overlay).

-spec 'gen_nb_server:handle_cast'(term(), nb_state()) -> nb_noreply().
'gen_nb_server:handle_cast'(_, _) -> error(overlay).

%% {inet_async, ListSock, Ref, {ok, CliSocket}} of prim_inet:async_accept/2, any other message goes to
%% the callback module
-spec 'gen_nb_server:handle_info'(term(), nb_state()) -> nb_noreply().
'gen_nb_server:handle_info'(_, _) -> error(overlay).

-spec 'gen_nb_server:terminate'(term(), nb_state()) -> ok.
'gen_nb_server:terminate'(_, _) -> error(overlay).

-spec 'gen_nb_server:code_change'(term(), nb_state(), term()) -> {ok, nb_state()}.
'gen_nb_server:code_change'(_, _, _) -> error(overlay).

%% the @spec: IpAddr = string() | tuple(), Port = integer(), Result = {ok, port()} | {error, any()}
-spec 'gen_nb_server:listen_on'(module(), string() | nb_ip_address(), integer()) -> {ok, port()} | {error, any()}.
'gen_nb_server:listen_on'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_receiver
%% ---------------------------------------------------------------------------------------------

%% -record(state, {sock, peer, recv_timeout_len, vnode_timeout_len, partition, vnode_mod, vnode, count})
%% with the declared field types
-type hr_state() :: {state, port() | undefined, term(), non_neg_integer(), non_neg_integer(),
                     non_neg_integer() | undefined, module(), pid() | undefined, non_neg_integer()}.

-spec 'riak_core_handoff_receiver:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_receiver:start_link'() -> error(overlay).

%% the socket goes into the field sock :: port() | undefined
-spec 'riak_core_handoff_receiver:set_socket'(pid(), port()) -> ok.
'riak_core_handoff_receiver:set_socket'(_, _) -> error(overlay).

-spec 'riak_core_handoff_receiver:supports_batching'() -> true.
'riak_core_handoff_receiver:supports_batching'() -> error(overlay).

-spec 'riak_core_handoff_receiver:init'([]) -> {ok, hr_state()}.
'riak_core_handoff_receiver:init'(_) -> error(overlay).

-spec 'riak_core_handoff_receiver:handle_call'({set_socket, port()}, {pid(), term()}, hr_state()) ->
          {reply, ok, hr_state()}.
'riak_core_handoff_receiver:handle_call'(_, _, _) -> error(overlay).

%% the socket is binary with {packet, 4} and {header, 1}: the data is the message type and a binary as tail
-spec 'riak_core_handoff_receiver:handle_info'({tcp_closed, port()} | {tcp_error, port(), term()} |
                                               {tcp, port(), nonempty_improper_list(byte(), binary())} | timeout,
                                               hr_state()) ->
          {stop, normal, hr_state()} | {noreply, hr_state(), non_neg_integer()}.
'riak_core_handoff_receiver:handle_info'(_, _) -> error(overlay).

%% the message type is one of the PT_MSG_* of riak_core_handoff.hrl, any other byte is answered with
%% PT_MSG_UNKNOWN; exits with {error, _} if the vnode fails or is the wrong node
-spec 'riak_core_handoff_receiver:process_message'(byte(), binary(), hr_state()) -> hr_state().
'riak_core_handoff_receiver:process_message'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_receiver:handle_cast'(term(), hr_state()) -> {noreply, hr_state()}.
'riak_core_handoff_receiver:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_handoff_receiver:terminate'(term(), hr_state()) -> ok.
'riak_core_handoff_receiver:terminate'(_, _) -> error(overlay).

-spec 'riak_core_handoff_receiver:code_change'(term(), hr_state(), term()) -> {ok, hr_state()}.
'riak_core_handoff_receiver:code_change'(_, _, _) -> error(overlay).

%% the second argument is the module with peername/1, the only caller passes inet
-spec 'riak_core_handoff_receiver:safe_peername'(port(), module()) ->
          {string(), inet:port_number()} | {unknown, unknown}.
'riak_core_handoff_receiver:safe_peername'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_listener_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_handoff_listener_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_listener_sup:start_link'() -> error(overlay).

-spec 'riak_core_handoff_listener_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_handoff_listener_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_receiver_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_handoff_receiver_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_receiver_sup:start_link'() -> error(overlay).

-spec 'riak_core_handoff_receiver_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_handoff_receiver_sup:init'(_) -> error(overlay).

%% the child is riak_core_handoff_receiver:start_link/0, which gives {ok, pid()} or an error
-spec 'riak_core_handoff_receiver_sup:start_receiver'() -> {ok, pid()} | {error, term()}.
'riak_core_handoff_receiver_sup:start_receiver'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_sender_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_handoff_sender_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_sender_sup:start_link'() -> error(overlay).

-spec 'riak_core_handoff_sender_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_handoff_sender_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_handoff_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_sup:start_link'() -> error(overlay).

-spec 'riak_core_handoff_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_handoff_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_manager
%% ---------------------------------------------------------------------------------------------

%% the record state. excl has no type in the declaration: it is the set that add_exclusion/2 fills.
-type hm_state() :: {state, sets:set({module(), riak_core_handoff_manager:index()}),
                     [riak_core_handoff_manager:handoff_status()]}.

%% the options of an outbound handoff, as send_handoff/8 says. Only size is read.
-type hm_opts() :: [{atom(), term()}].

%% the size of a transfer once it is known, see the field size of handoff_status()
-type hm_size() :: {non_neg_integer(), bytes | objects} | undefined.

%% the list that calc_stats/1 builds
-type hm_stat() :: {objs_total, non_neg_integer()}
                 | {objs_per_s | bytes_per_s, integer()}
                 | {last_update, erlang:timestamp()}
                 | {size, hm_size()}
                 | {pct_done_decimal, float() | undefined}.

%% what build_status/1 makes of a handoff_status(): the elements of the reply of status/1.
%% The partitions and the module of an inbound handoff are undefined until set_recv_data/2.
-type hm_status_prop() :: {mod, module() | undefined}
                        | {src_partition | target_partition, riak_core_handoff_manager:index() | undefined}
                        | {src_node | target_node, node()}
                        | {direction, inbound | outbound}
                        | {status, any()}
                        | {start_ts, tuple()}
                        | {sender_pid, pid()}
                        | {stats, no_stats | [hm_stat()]}
                        | {type, riak_core_handoff_manager:ho_type() | undefined}.
-type hm_status() :: {status_v2, [hm_status_prop()]}.

%% the argument of status/1: all handoffs or the ones with this value for this key of the status
-type hm_filter() :: none | {atom(), term()}.

%% the requests of handle_call/3 (no catch-all clause). Nothing in riak_core sends xfer_status.
-type hm_call() :: {get_exclusions, module()}
                 | {add_outbound, riak_core_handoff_manager:ho_type(), module(), riak_core_handoff_manager:index(),
                    riak_core_handoff_manager:index(), node(), pid(), hm_opts()}
                 | {add_inbound}
                 | {set_recv_data, pid(), proplists:proplist()}
                 | {xfer_status, riak_core_handoff_manager:handoff_status()}
                 | {status, hm_filter()}
                 | {set_concurrency, non_neg_integer()}
                 | get_concurrency
                 | {kill_in_direction, inbound | outbound}.

%% the requests of handle_cast/2 (no catch-all clause). kill_xfer/3 says tuple() for the transfer: the
%% receiving side kills {Mod, undefined, Partition}, which is not a mod_src_tgt().
-type hm_cast() :: {del_exclusion | add_exclusion, {module(), riak_core_handoff_manager:index()}}
                 | {status_update, riak_core_handoff_manager:mod_src_tgt(), riak_core_handoff_manager:ho_stats()}
                 | {send_handoff, riak_core_handoff_manager:ho_type(), module(),
                    {riak_core_handoff_manager:index(), riak_core_handoff_manager:index()}, node(),
                    {module(), atom()}}
                 | {kill_xfer, tuple(), any()}.

-spec 'riak_core_handoff_manager:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_handoff_manager:start_link'() -> error(overlay).

-spec 'riak_core_handoff_manager:init'([]) -> {ok, hm_state()}.
'riak_core_handoff_manager:init'(_) -> error(overlay).

%% the reply is {ok, Sender} also for a handoff that runs already
-spec 'riak_core_handoff_manager:add_outbound'(riak_core_handoff_manager:ho_type(), module(),
                                               riak_core_handoff_manager:index(), node(), pid(), hm_opts()) ->
          {ok, pid()} | {error, max_concurrency}.
'riak_core_handoff_manager:add_outbound'(_, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:add_outbound'(riak_core_handoff_manager:ho_type(), module(),
                                               riak_core_handoff_manager:index(),
                                               riak_core_handoff_manager:index(), node(), pid(), hm_opts()) ->
          {ok, pid()} | {error, max_concurrency}.
'riak_core_handoff_manager:add_outbound'(_, _, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:add_inbound'() -> {ok, pid()} | {error, max_concurrency}.
'riak_core_handoff_manager:add_inbound'() -> error(overlay).

-spec 'riak_core_handoff_manager:status'() -> [hm_status()].
'riak_core_handoff_manager:status'() -> error(overlay).

-spec 'riak_core_handoff_manager:status'(hm_filter()) -> [hm_status()].
'riak_core_handoff_manager:status'(_) -> error(overlay).

%% the limit is the first argument of lists:split/2
-spec 'riak_core_handoff_manager:set_concurrency'(non_neg_integer()) -> ok.
'riak_core_handoff_manager:set_concurrency'(_) -> error(overlay).

-spec 'riak_core_handoff_manager:get_concurrency'() -> non_neg_integer().
'riak_core_handoff_manager:get_concurrency'() -> error(overlay).

-spec 'riak_core_handoff_manager:kill_handoffs'() -> ok.
'riak_core_handoff_manager:kill_handoffs'() -> error(overlay).

-spec 'riak_core_handoff_manager:add_exclusion'(module(), riak_core_handoff_manager:index()) -> ok.
'riak_core_handoff_manager:add_exclusion'(_, _) -> error(overlay).

-spec 'riak_core_handoff_manager:remove_exclusion'(module(), riak_core_handoff_manager:index()) -> ok.
'riak_core_handoff_manager:remove_exclusion'(_, _) -> error(overlay).

-spec 'riak_core_handoff_manager:get_exclusions'(module()) -> {ok, [riak_core_handoff_manager:index()]}.
'riak_core_handoff_manager:get_exclusions'(_) -> error(overlay).

%% the replies in the order of the clauses
-spec 'riak_core_handoff_manager:handle_call'(hm_call(), {pid(), term()}, hm_state()) ->
          {reply,
           {ok, [riak_core_handoff_manager:index()]} | {ok, pid()} | {error, max_concurrency} | ok |
           not_found | in_progress | [hm_status()] | non_neg_integer(),
           hm_state()}.
'riak_core_handoff_manager:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:handle_cast'(hm_cast(), hm_state()) -> {noreply, hm_state()}.
'riak_core_handoff_manager:handle_cast'(_, _) -> error(overlay).

%% only the monitors of the transport and vnode processes are handled, there is no catch-all clause
-spec 'riak_core_handoff_manager:handle_info'({'DOWN', reference(), process, pid(), term()}, hm_state()) ->
          {noreply, hm_state()}.
'riak_core_handoff_manager:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_handoff_manager:terminate'(term(), hm_state()) -> ok.
'riak_core_handoff_manager:terminate'(_, _) -> error(overlay).

-spec 'riak_core_handoff_manager:code_change'(term(), hm_state(), term()) -> {ok, hm_state()}.
'riak_core_handoff_manager:code_change'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:build_status'(riak_core_handoff_manager:handoff_status()) -> hm_status().
'riak_core_handoff_manager:build_status'(_) -> error(overlay).

%% no_stats until the first status_update/2 of the sender
-spec 'riak_core_handoff_manager:calc_stats'(riak_core_handoff_manager:handoff_status()) -> no_stats | [hm_stat()].
'riak_core_handoff_manager:calc_stats'(_) -> error(overlay).

%% the argument is the field size of handoff_status(), which says function() for the fun: it is called
%% without arguments and its result goes to calc_pct_done/3
-spec 'riak_core_handoff_manager:get_size'({fun(() -> hm_size()), dynamic} | hm_size()) -> hm_size().
'riak_core_handoff_manager:get_size'(_) -> error(overlay).

%% objects and bytes sent so far, and the size from get_size/1
-spec 'riak_core_handoff_manager:calc_pct_done'(non_neg_integer(), non_neg_integer(), hm_size()) ->
          float() | undefined.
'riak_core_handoff_manager:calc_pct_done'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:filter'(hm_filter()) -> fun((hm_status()) -> boolean()).
'riak_core_handoff_manager:filter'(_) -> error(overlay).

%% the filter of a resize transfer, a predicate on the key of an object
-spec 'riak_core_handoff_manager:resize_transfer_filter'(riak_core_ring:riak_core_ring(), module(),
                                                         riak_core_handoff_manager:index(),
                                                         riak_core_handoff_manager:index()) ->
          riak_core_handoff_manager:predicate().
'riak_core_handoff_manager:resize_transfer_filter'(_, _, _, _) -> error(overlay).

%% the fun gets a key that was not sent and the future indexes seen so far (send_handoff/8 starts with
%% ordsets:new())
-spec 'riak_core_handoff_manager:resize_transfer_notsent_fun'(riak_core_ring:riak_core_ring(), module(),
                                                              riak_core_handoff_manager:index()) ->
          fun((term(), ordsets:ordset(riak_core_handoff_manager:index())) ->
                  ordsets:ordset(riak_core_handoff_manager:index())).
'riak_core_handoff_manager:resize_transfer_notsent_fun'(_, _, _) -> error(overlay).

%% the third and fourth argument are Mod:nval_map(Ring) (bucket to n_val) and the default n_val, both
%% undefined if the ring does not shrink. The bucket is what Mod:object_info/1 says, a term of the vnode module.
-spec 'riak_core_handoff_manager:record_seen_index'(riak_core_ring:riak_core_ring(), boolean(),
                                                    [{term(), integer()}] | undefined, integer() | undefined,
                                                    module(), riak_core_handoff_manager:index(), term(),
                                                    ordsets:ordset(riak_core_handoff_manager:index())) ->
          ordsets:ordset(riak_core_handoff_manager:index()).
'riak_core_handoff_manager:record_seen_index'(_, _, _, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:get_concurrency_limit'() -> non_neg_integer().
'riak_core_handoff_manager:get_concurrency_limit'() -> error(overlay).

-spec 'riak_core_handoff_manager:handoff_concurrency_limit_reached'() -> boolean().
'riak_core_handoff_manager:handoff_concurrency_limit_reached'() -> error(overlay).

%% as send_handoff/8, with the handoffs of the state for its list()
-spec 'riak_core_handoff_manager:send_handoff'(riak_core_handoff_manager:ho_type(),
                                               {module(), riak_core_handoff_manager:index(),
                                                riak_core_handoff_manager:index()},
                                               node(), pid(), [riak_core_handoff_manager:handoff_status()],
                                               hm_opts()) ->
          {ok, riak_core_handoff_manager:handoff_status()} | {error, max_concurrency} |
          {false, riak_core_handoff_manager:handoff_status()}.
'riak_core_handoff_manager:send_handoff'(_, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:receive_handoff'() ->
          {ok, riak_core_handoff_manager:handoff_status()} | {error, max_concurrency}.
'riak_core_handoff_manager:receive_handoff'() -> error(overlay).

%% the dict is the field stats of handoff_status(): objs, bytes and last_update
-spec 'riak_core_handoff_manager:update_stats'(riak_core_handoff_manager:ho_stats(),
                                               riak_core_handoff_manager:riak_core_handoff_dict()) ->
          riak_core_handoff_manager:riak_core_handoff_dict().
'riak_core_handoff_manager:update_stats'(_, _) -> error(overlay).

%% checks the value of the option size, the result is the field size of handoff_status()
-spec 'riak_core_handoff_manager:validate_size'(term()) ->
          {function(), dynamic} | {non_neg_integer(), bytes | objects} | undefined.
'riak_core_handoff_manager:validate_size'(_) -> error(overlay).

%% the transfer and the reason are the arguments of kill_xfer/3
-spec 'riak_core_handoff_manager:kill_xfer_i'(tuple(), any(), [riak_core_handoff_manager:handoff_status()]) ->
          [riak_core_handoff_manager:handoff_status()].
'riak_core_handoff_manager:kill_xfer_i'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_manager:handoff_change_enabled_setting'(enable | disable,
                                                                 inbound | outbound | both) -> ok.
'riak_core_handoff_manager:handoff_change_enabled_setting'(_, _) -> error(overlay).

-spec 'riak_core_handoff_manager:handoff_enable'(inbound | outbound) -> ok.
'riak_core_handoff_manager:handoff_enable'(_) -> error(overlay).

-spec 'riak_core_handoff_manager:handoff_disable'(inbound | outbound) -> ok.
'riak_core_handoff_manager:handoff_disable'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_handoff_sender
%% ---------------------------------------------------------------------------------------------

%% the record ho_acc, the accumulator of the fold: ack, error, filter, module, parent, socket, src_target,
%% stats, total_objects, total_bytes, use_batching, item_queue, item_queue_length, item_queue_byte_size,
%% acksync_threshold, acksync_timer, type, notsent_acc, notsent_fun
-type hs_acc() :: {ho_acc, non_neg_integer(), ok | {error, any()}, function(), module(), pid(), any(),
                   {non_neg_integer(), non_neg_integer()}, riak_core_handoff_sender:ho_stats(),
                   non_neg_integer(), non_neg_integer(), boolean(), [binary()], non_neg_integer(),
                   non_neg_integer(), non_neg_integer(), timer:tref() | undefined,
                   riak_core_handoff_sender:ho_type(), term(), function() | undefined}.

%% the options that riak_core_handoff_manager:send_handoff/8 makes: src_partition, target_partition, filter,
%% notsent_acc0, notsent_fun. get_filter/1 says proplists:proplist().
-type hs_opts() :: proplists:proplist().

%% a partition. The module says non_neg_integer() for it (src_target of ho_acc, maybe_send_status/2).
-type hs_partition() :: non_neg_integer().

%% the fun for the keys that the filter rejects: key and accumulator (notsent_acc of ho_acc, a term()
%% for this module) to the new accumulator
-type hs_notsent_fun() :: fun((term(), term()) -> term()).

%% inet:port_number(); the module does not mention inet
-type hs_port() :: 0..65535.

%% the third argument is what riak_core_handoff_sender_sup:start_sender/5 makes, the fourth the vnode
-spec 'riak_core_handoff_sender:start_link'(node(), module(), {riak_core_handoff_sender:ho_type(), hs_opts()},
                                            pid()) -> {ok, pid()}.
'riak_core_handoff_sender:start_link'(_, _, _, _) -> error(overlay).

%% target node, vnode module, type, options, vnode, source node, source and target partition.
%% Ends with ok or with an exit or throw that start_fold/4 handles.
-spec 'riak_core_handoff_sender:start_fold_'(node(), module(), riak_core_handoff_sender:ho_type(), hs_opts(),
                                             pid(), node(), hs_partition(), hs_partition()) -> ok.
'riak_core_handoff_sender:start_fold_'(_, _, _, _, _, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_sender:start_fold'(node(), module(), {riak_core_handoff_sender:ho_type(), hs_opts()},
                                            pid()) -> ok.
'riak_core_handoff_sender:start_fold'(_, _, _, _) -> error(overlay).

-spec 'riak_core_handoff_sender:start_visit_item_timer'() -> {ok, timer:tref()} | {error, term()}.
'riak_core_handoff_sender:start_visit_item_timer'() -> error(overlay).

%% the fold fun of the request to the vnode: key and value of an object, as encode_handoff_item/2 gets them
-spec 'riak_core_handoff_sender:visit_item'(term(), term(), hs_acc()) -> hs_acc().
'riak_core_handoff_sender:visit_item'(_, _, _) -> error(overlay).

-spec 'riak_core_handoff_sender:visit_item2'(term(), term(), hs_acc()) -> hs_acc().
'riak_core_handoff_sender:visit_item2'(_, _, _) -> error(overlay).

%% fun, accumulator, key. Without a fun the accumulator becomes undefined.
-spec 'riak_core_handoff_sender:handle_not_sent_item'(hs_notsent_fun() | undefined, term(), term()) -> term().
'riak_core_handoff_sender:handle_not_sent_item'(_, _, _) -> error(overlay).

%% the first argument is the item_queue of the accumulator, newest first
-spec 'riak_core_handoff_sender:send_objects'([binary()], hs_acc()) -> hs_acc().
'riak_core_handoff_sender:send_objects'(_, _) -> error(overlay).

%% the reply of riak_core_handoff_listener to handoff_ip, error for a failed rpc
-spec 'riak_core_handoff_sender:get_handoff_ip'(node()) -> {ok, string()} | error.
'riak_core_handoff_sender:get_handoff_ip'(_) -> error(overlay).

%% the reply of riak_core_handoff_listener to handoff_port. Its record says integer(), the port goes to
%% gen_tcp:connect/4.
-spec 'riak_core_handoff_sender:get_handoff_port'(node()) -> {ok, hs_port()}.
'riak_core_handoff_sender:get_handoff_port'(_) -> error(overlay).

%% the timeout of gen_tcp:recv/3
-spec 'riak_core_handoff_sender:get_handoff_receive_timeout'() -> timeout().
'riak_core_handoff_sender:get_handoff_receive_timeout'() -> error(overlay).

%% seconds since the start of the fold
-spec 'riak_core_handoff_sender:end_fold_time'(erlang:timestamp()) -> float().
'riak_core_handoff_sender:end_fold_time'(_) -> error(overlay).

-spec 'riak_core_handoff_sender:incr_objs'(riak_core_handoff_sender:ho_stats()) ->
          riak_core_handoff_sender:ho_stats().
'riak_core_handoff_sender:incr_objs'(_) -> error(overlay).

%% seconds, the argument of future_now/1
-spec 'riak_core_handoff_sender:get_status_interval'() -> pos_integer().
'riak_core_handoff_sender:get_status_interval'() -> error(overlay).

-spec 'riak_core_handoff_sender:get_src_partition'(hs_opts()) -> hs_partition().
'riak_core_handoff_sender:get_src_partition'(_) -> error(overlay).

-spec 'riak_core_handoff_sender:get_target_partition'(hs_opts()) -> hs_partition().
'riak_core_handoff_sender:get_target_partition'(_) -> error(overlay).

-spec 'riak_core_handoff_sender:get_notsent_acc0'(hs_opts()) -> term().
'riak_core_handoff_sender:get_notsent_acc0'(_) -> error(overlay).

%% riak_core_handoff_manager gives undefined if the transfer is not a resize
-spec 'riak_core_handoff_sender:get_notsent_fun'(hs_opts()) -> hs_notsent_fun() | undefined.
'riak_core_handoff_sender:get_notsent_fun'(_) -> error(overlay).

-spec 'riak_core_handoff_sender:remote_supports_batching'(node()) -> boolean().
'riak_core_handoff_sender:remote_supports_batching'(_) -> error(overlay).

%% the result is the options for the fold request that Module:handoff_started/2 gives
-spec 'riak_core_handoff_sender:maybe_call_handoff_started'(module(), hs_partition()) -> [term()].
'riak_core_handoff_sender:maybe_call_handoff_started'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_gossip
%% ---------------------------------------------------------------------------------------------

%% the record state: the gossip messages that may still be sent before the next reset_tokens
-type gossip_state() :: {state, non_neg_integer()}.

%% rand:state() spelled out as in rand.erl of stdlib, because riak_core_gossip does not mention rand:
%% the handler of the algorithm and the state of the algorithm (alg_state() ends in term())
-type gossip_rand_state() ::
        {#{type := atom(), bits => non_neg_integer(), weak_low_bits => non_neg_integer(),
           max => non_neg_integer(),
           next := fun((term()) -> {non_neg_integer(), term()}),
           uniform => fun((gossip_rand_state()) -> {float(), gossip_rand_state()}),
           uniform_n => fun((pos_integer(), gossip_rand_state()) -> {pos_integer(), gossip_rand_state()}),
           jump => fun((gossip_rand_state()) -> gossip_rand_state())},
         term()}.

%% the seed that attempt_simple_transfer/7 threads through riak_core_rand:uniform_s/2: at first the
%% timestamp of riak_core_rand:rand_seed/0, then the state that uniform_s/2 gives back
-type gossip_seed() :: erlang:timestamp() | gossip_rand_state().

-spec 'riak_core_gossip:distribute_ring'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:distribute_ring'(_) -> error(overlay).

-spec 'riak_core_gossip:send_ring'(node()) -> ok.
'riak_core_gossip:send_ring'(_) -> error(overlay).

%% from node, to node
-spec 'riak_core_gossip:send_ring'(node(), node()) -> ok.
'riak_core_gossip:send_ring'(_, _) -> error(overlay).

-spec 'riak_core_gossip:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_gossip:start_link'() -> error(overlay).

-spec 'riak_core_gossip:stop'() -> ok.
'riak_core_gossip:stop'() -> error(overlay).

-spec 'riak_core_gossip:rejoin'(node(), riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:rejoin'(_, _) -> error(overlay).

-spec 'riak_core_gossip:random_gossip'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:random_gossip'(_) -> error(overlay).

%% the node is the one whose children in the tree of the active members get the ring
-spec 'riak_core_gossip:recursive_gossip'(riak_core_ring:riak_core_ring(), node()) -> ok.
'riak_core_gossip:recursive_gossip'(_, _) -> error(overlay).

-spec 'riak_core_gossip:recursive_gossip'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:recursive_gossip'(_) -> error(overlay).

-spec 'riak_core_gossip:random_recursive_gossip'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:random_recursive_gossip'(_) -> error(overlay).

-spec 'riak_core_gossip:init'([]) -> {ok, gossip_state()}.
'riak_core_gossip:init'(_) -> error(overlay).

-spec 'riak_core_gossip:handle_call'(term(), {pid(), term()}, gossip_state()) -> {reply, ok, gossip_state()}.
'riak_core_gossip:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_gossip:handle_cast'(term(), gossip_state()) -> {noreply, gossip_state()}.
'riak_core_gossip:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_gossip:handle_info'(term(), gossip_state()) -> {noreply, gossip_state()}.
'riak_core_gossip:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_gossip:terminate'(term(), gossip_state()) -> ok.
'riak_core_gossip:terminate'(_, _) -> error(overlay).

-spec 'riak_core_gossip:code_change'(term(), gossip_state(), term()) -> {ok, gossip_state()}.
'riak_core_gossip:code_change'(_, _, _) -> error(overlay).

%% the timer of erlang:send_after/3
-spec 'riak_core_gossip:schedule_next_reset'() -> reference().
'riak_core_gossip:schedule_next_reset'() -> error(overlay).

%% the fun of riak_core_ring_manager:ring_trans/2: the ring of this node and the arguments, here the ring
%% of the other node
-spec 'riak_core_gossip:reconcile'(riak_core_ring:riak_core_ring(), [riak_core_ring:riak_core_ring(), ...]) ->
          ignore | {reconciled_ring, riak_core_ring:riak_core_ring()}.
'riak_core_gossip:reconcile'(_, _) -> error(overlay).

-spec 'riak_core_gossip:log_membership_changes'(riak_core_ring:riak_core_ring(),
                                                riak_core_ring:riak_core_ring()) -> ok.
'riak_core_gossip:log_membership_changes'(_, _) -> error(overlay).

%% the sorted results of riak_core_ring:all_member_status/1 for the old and the new ring
-spec 'riak_core_gossip:do_log_membership_changes'([{node(), riak_core_ring:member_status()}],
                                                   [{node(), riak_core_ring:member_status()}]) -> ok.
'riak_core_gossip:do_log_membership_changes'(_, _) -> error(overlay).

-spec 'riak_core_gossip:log_node_changed'(node(), riak_core_ring:member_status(),
                                          riak_core_ring:member_status()) -> ok.
'riak_core_gossip:log_node_changed'(_, _, _) -> error(overlay).

-spec 'riak_core_gossip:log_node_added'(node(), riak_core_ring:member_status()) -> ok.
'riak_core_gossip:log_node_added'(_, _) -> error(overlay).

-spec 'riak_core_gossip:log_node_removed'(node(), riak_core_ring:member_status()) -> ok.
'riak_core_gossip:log_node_removed'(_, _) -> error(overlay).

-spec 'riak_core_gossip:remove_from_cluster'(riak_core_ring:riak_core_ring(), node()) ->
          riak_core_ring:riak_core_ring().
'riak_core_gossip:remove_from_cluster'(_, _) -> error(overlay).

%% the seed is the one of riak_core_rand:rand_seed/0
-spec 'riak_core_gossip:remove_from_cluster'(riak_core_ring:riak_core_ring(), node(), erlang:timestamp()) ->
          riak_core_ring:riak_core_ring().
'riak_core_gossip:remove_from_cluster'(_, _, _) -> error(overlay).

%% seed, ring, its owners and the node that leaves. riak_core_ring:all_owners/1 says term() for an owner.
-spec 'riak_core_gossip:attempt_simple_transfer'(erlang:timestamp(), riak_core_ring:riak_core_ring(),
                                                 [{integer(), node()}], node()) ->
          {ok, riak_core_ring:riak_core_ring()} | target_n_fail.
'riak_core_gossip:attempt_simple_transfer'(_, _, _, _) -> error(overlay).

%% seed, ring, the owners still to visit, target_n_val, the node that leaves, the position in the ring,
%% and for each claiming member the position where it was seen last
-spec 'riak_core_gossip:attempt_simple_transfer'(gossip_seed(), riak_core_ring:riak_core_ring(),
                                                 [{integer(), node()}], pos_integer(), node(),
                                                 non_neg_integer(), [{node(), integer()}]) ->
          {ok, riak_core_ring:riak_core_ring()} | target_n_fail.
'riak_core_gossip:attempt_simple_transfer'(_, _, _, _, _, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% types that several sections use
%% ---------------------------------------------------------------------------------------------

%% a handler of a gen_event manager, the "Handler" of the @spec of riak_core:add_guarded_event_handler/3
%% (it is gen_event:handler(), but riak_core does not mention gen_event)
-type core_handler() :: module() | {module(), term()}.

%% the "ExitFun" of the @spec of riak_core:add_guarded_event_handler/4: the guard calls it with the handler
%% and the reason of its exit and drops the result
-type core_exit_fun() :: fun((core_handler(), term()) -> term()).

%% an entry of the lists that register/2 keeps in the application environment (vnode_modules,
%% bucket_fixups, ...): the application, undefined if it is not known, and its module
-type core_app_mod() :: {atom(), module()}.

%% a health check of a service: riak_core_node_watcher applies it to [ServicePid | Args].
%% riak_core_node_watcher:service_up/3 calls it mfa(), which has an arity in the third place.
-type core_health_mfa() :: {module(), atom(), [term()]}.

%% ---------------------------------------------------------------------------------------------
%% riak_core
%% ---------------------------------------------------------------------------------------------

%% the errors of a join that got past the check for a join with the own node
-type core_join_error() :: not_reachable | unable_to_get_join_ring | node_still_starting |
                           not_single_node | different_ring_sizes.

%% the properties of register/2. The permissions are stored and never read in riak_core_lite; in riak_core
%% they are the names of the permissions of the application.
-type core_register_prop() :: {bucket_fixup, module()} | {repl_helper, module()} | {vnode_module, module()} |
                              {health_check, core_health_mfa()} | {bucket_validator, module()} |
                              {stat_mod, module()} | {permissions, [atom()]} | {auth_mod, {atom(), module()}}.

-spec 'riak_core:stop'() -> ok.
'riak_core:stop'() -> error(overlay).

%% the reason is only logged, with ~p; the callers pass a string
-spec 'riak_core:stop'(term()) -> ok.
'riak_core:stop'(_) -> error(overlay).

-spec 'riak_core:join'(node() | string()) -> ok | {error, self_join | core_join_error()}.
'riak_core:join'(_) -> error(overlay).

-spec 'riak_core:staged_join'(node() | string()) -> ok | {error, self_join | core_join_error()}.
'riak_core:staged_join'(_) -> error(overlay).

-spec 'riak_core:join'(node() | string(), boolean()) -> ok | {error, self_join | core_join_error()}.
'riak_core:join'(_, _) -> error(overlay).

%% the first argument is the own node
-spec 'riak_core:join'(node(), node(), boolean()) -> ok | {error, self_join | core_join_error()}.
'riak_core:join'(_, _, _) -> error(overlay).

%% the first argument is not used, the callers pass node(); then the node to join, Rejoin and Auto
-spec 'riak_core:join'(node(), node(), boolean(), boolean()) -> ok | {error, core_join_error()}.
'riak_core:join'(_, _, _, _) -> error(overlay).

%% the result of riak_core_ring_manager:get_raw_ring/0 on the other node, or the error of the rpc
-spec 'riak_core:get_other_ring'(node()) -> {ok, riak_core_ring:riak_core_ring()} | {badrpc, term()}.
'riak_core:get_other_ring'(_) -> error(overlay).

-spec 'riak_core:standard_join'(node(), boolean(), boolean()) -> ok | {error, core_join_error()}.
'riak_core:standard_join'(_, _, _) -> error(overlay).

%% the argument is the result of init:get_status/0
-spec 'riak_core:init_complete'({starting | started | stopping, term()}) -> boolean().
'riak_core:init_complete'(_) -> error(overlay).

%% the second argument is the ring of the node to join
-spec 'riak_core:standard_join'(node(), riak_core_ring:riak_core_ring(), boolean(), boolean()) ->
          ok | {error, node_still_starting | not_single_node | different_ring_sizes}.
'riak_core:standard_join'(_, _, _, _) -> error(overlay).

-spec 'riak_core:maybe_auto_join'(boolean(), node(), riak_core_ring:riak_core_ring()) ->
          riak_core_ring:riak_core_ring().
'riak_core:maybe_auto_join'(_, _, _) -> error(overlay).

-spec 'riak_core:remove'(node()) -> ok | {error, not_member | only_member}.
'riak_core:remove'(_) -> error(overlay).

-spec 'riak_core:standard_remove'(node()) -> ok.
'riak_core:standard_remove'(_) -> error(overlay).

-spec 'riak_core:down'(node()) -> ok | {error, is_up | not_member | only_member}.
'riak_core:down'(_) -> error(overlay).

-spec 'riak_core:leave'() -> ok | {error, not_member | only_member | already_leaving}.
'riak_core:leave'() -> error(overlay).

-spec 'riak_core:standard_leave'(node()) -> ok.
'riak_core:standard_leave'(_) -> error(overlay).

%% the @spec says term(); it is the result of remove/1
-spec 'riak_core:remove_from_cluster'(node()) -> ok | {error, not_member | only_member}.
'riak_core:remove_from_cluster'(_) -> error(overlay).

-spec 'riak_core:vnode_modules'() -> [core_app_mod()].
'riak_core:vnode_modules'() -> error(overlay).

-spec 'riak_core:bucket_fixups'() -> [core_app_mod()].
'riak_core:bucket_fixups'() -> error(overlay).

-spec 'riak_core:bucket_validators'() -> [core_app_mod()].
'riak_core:bucket_validators'() -> error(overlay).

-spec 'riak_core:stat_mods'() -> [core_app_mod()].
'riak_core:stat_mods'() -> error(overlay).

-spec 'riak_core:health_check'(atom()) -> undefined | core_health_mfa().
'riak_core:health_check'(_) -> error(overlay).

%% the application that was given, or the one of the calling process, or the one that has the module;
%% undefined if there is none. register/2 also calls it with the MFA of a health check as the module.
-spec 'riak_core:get_app'(atom(), module()) -> atom().
'riak_core:get_app'(_, _) -> error(overlay).

-spec 'riak_core:register'([core_register_prop()]) -> ok.
'riak_core:register'(_) -> error(overlay).

%% the application is undefined if register/1 was called
-spec 'riak_core:register'(atom(), [core_register_prop()]) -> ok.
'riak_core:register'(_, _) -> error(overlay).

%% the second argument is a module, or the permissions of the application for the key permissions;
%% the third is the key in the application environment
-spec 'riak_core:register_mod'(atom(), module() | [atom()], atom()) -> ok.
'riak_core:register_mod'(_, _, _) -> error(overlay).

%% only used for health_checks
-spec 'riak_core:register_metadata'(atom(), core_health_mfa(), atom()) -> ok.
'riak_core:register_metadata'(_, _, _) -> error(overlay).

%% only used for auth_mods: the type of the authentication and its module
-spec 'riak_core:register_proplist'({atom(), module()}, atom()) -> ok.
'riak_core:register_proplist'(_, _) -> error(overlay).

%% as the @spec says; HandlerMod is the registered name of the event manager
-spec 'riak_core:add_guarded_event_handler'(module(), core_handler(), list()) -> ok | {error, term()}.
'riak_core:add_guarded_event_handler'(_, _, _) -> error(overlay).

%% as the @spec says, and add_guarded_event_handler/3 passes undefined for the ExitFun
-spec 'riak_core:add_guarded_event_handler'(module(), core_handler(), list(), undefined | core_exit_fun()) ->
          ok | {error, term()}.
'riak_core:add_guarded_event_handler'(_, _, _, _) -> error(overlay).

%% as the @spec says: the result of terminate/2 of the handler, as for gen_event:delete_handler/3
-spec 'riak_core:delete_guarded_event_handler'(module(), core_handler(), term()) ->
          term() | {error, module_not_found} | {'EXIT', term()}.
'riak_core:delete_guarded_event_handler'(_, _, _) -> error(overlay).

%% {ok, undefined} if no running application has the module
-spec 'riak_core:app_for_module'(module()) -> {ok, atom()}.
'riak_core:app_for_module'(_) -> error(overlay).

%% the first argument is the result of application:which_applications/0
-spec 'riak_core:app_for_module'([{atom(), string(), string()}], module()) -> {ok, atom()}.
'riak_core:app_for_module'(_, _) -> error(overlay).

-spec 'riak_core:wait_for_application'(atom()) -> ok.
'riak_core:wait_for_application'(_) -> error(overlay).

%% the second argument is the time waited so far, in milliseconds
-spec 'riak_core:wait_for_application'(atom(), non_neg_integer()) -> ok.
'riak_core:wait_for_application'(_, _) -> error(overlay).

-spec 'riak_core:wait_for_service'(atom()) -> ok.
'riak_core:wait_for_service'(_) -> error(overlay).

-spec 'riak_core:wait_for_service'(atom(), non_neg_integer()) -> ok.
'riak_core:wait_for_service'(_, _) -> error(overlay).

%% the default is riak; the prefix is the first part of the name of a metric
-spec 'riak_core:stat_prefix'() -> atom().
'riak_core:stat_prefix'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_app
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_app:start'(application:start_type(), term()) -> {ok, pid()} | {error, term()}.
'riak_core_app:start'(_, _) -> error(overlay).

-spec 'riak_core_app:stop'(term()) -> ok.
'riak_core_app:stop'(_) -> error(overlay).

%% throws {error, invalid_ring_state_dir} if the directory cannot be created
-spec 'riak_core_app:validate_ring_state_directory_exists'() -> ok.
'riak_core_app:validate_ring_state_directory_exists'() -> error(overlay).

-spec 'riak_core_app:start_riak_core_sup'() -> {ok, pid()} | {error, term()}.
'riak_core_app:start_riak_core_sup'() -> error(overlay).

-spec 'riak_core_app:register_applications'() -> ok.
'riak_core_app:register_applications'() -> error(overlay).

-spec 'riak_core_app:add_ring_event_handler'() -> ok.
'riak_core_app:add_ring_event_handler'() -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_sup:start_link'() -> error(overlay).

-spec 'riak_core_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_eventhandler_guard
%% ---------------------------------------------------------------------------------------------

%% the record state: handlermod, handler, exitfun (the fields have no types)
-type core_guard_state() :: {state, module(), core_handler(), undefined | core_exit_fun()}.

-spec 'riak_core_eventhandler_guard:start_link'(module(), core_handler(), list()) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_eventhandler_guard:start_link'(_, _, _) -> error(overlay).

-spec 'riak_core_eventhandler_guard:start_link'(module(), core_handler(), list(), undefined | core_exit_fun()) ->
          {ok, pid()} | ignore | {error, term()}.
'riak_core_eventhandler_guard:start_link'(_, _, _, _) -> error(overlay).

%% [HandlerMod, Handler, Args, ExitFun]
-spec 'riak_core_eventhandler_guard:init'([module() | core_handler() | list() | undefined | core_exit_fun()]) ->
          {ok, core_guard_state()}.
'riak_core_eventhandler_guard:init'(_) -> error(overlay).

-spec 'riak_core_eventhandler_guard:handle_call'(term(), {pid(), term()}, core_guard_state()) ->
          {reply, ok, core_guard_state()}.
'riak_core_eventhandler_guard:handle_call'(_, _, _) -> error(overlay).

-spec 'riak_core_eventhandler_guard:handle_cast'(term(), core_guard_state()) -> {noreply, core_guard_state()}.
'riak_core_eventhandler_guard:handle_cast'(_, _) -> error(overlay).

%% the message of interest is {gen_event_EXIT, Handler, Reason}; the handler in the stop reason is taken from it
-spec 'riak_core_eventhandler_guard:handle_info'(term(), core_guard_state()) ->
          {noreply, core_guard_state()} | {stop, normal | {gen_event_EXIT, term()}, core_guard_state()}.
'riak_core_eventhandler_guard:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_eventhandler_guard:terminate'(term(), core_guard_state()) -> ok.
'riak_core_eventhandler_guard:terminate'(_, _) -> error(overlay).

-spec 'riak_core_eventhandler_guard:code_change'(term(), core_guard_state(), term()) -> {ok, core_guard_state()}.
'riak_core_eventhandler_guard:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_eventhandler_sup
%% ---------------------------------------------------------------------------------------------

-spec 'riak_core_eventhandler_sup:start_guarded_handler'(module(), core_handler(), list()) -> ok | {error, term()}.
'riak_core_eventhandler_sup:start_guarded_handler'(_, _, _) -> error(overlay).

%% the guard never starts with {ok, Pid, Info}, so the result of supervisor:start_child/2 that is left
%% is the error
-spec 'riak_core_eventhandler_sup:start_guarded_handler'(module(), core_handler(), list(),
                                                         undefined | core_exit_fun()) ->
          ok | {error, term()}.
'riak_core_eventhandler_sup:start_guarded_handler'(_, _, _, _) -> error(overlay).

%% the result of gen_event:delete_handler/3
-spec 'riak_core_eventhandler_sup:stop_guarded_handler'(module(), core_handler(), term()) ->
          term() | {error, module_not_found} | {'EXIT', term()}.
'riak_core_eventhandler_sup:stop_guarded_handler'(_, _, _) -> error(overlay).

-spec 'riak_core_eventhandler_sup:handler_spec'(module(), core_handler(), list(), undefined | core_exit_fun()) ->
          supervisor:child_spec().
'riak_core_eventhandler_sup:handler_spec'(_, _, _, _) -> error(overlay).

-spec 'riak_core_eventhandler_sup:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_eventhandler_sup:start_link'() -> error(overlay).

-spec 'riak_core_eventhandler_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'riak_core_eventhandler_sup:init'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_node_watcher_events
%% ---------------------------------------------------------------------------------------------

%% a callback gets the services that changed (at first all services), the result is dropped.
%% A service is the Id :: atom() of riak_core_node_watcher:service_up/3.
-type core_nwe_callback() :: fun(([atom()]) -> term()).

%% the record state: callback (no type)
-type core_nwe_state() :: {state, core_nwe_callback()}.

%% gen_event:start_link/1 has no ignore
-spec 'riak_core_node_watcher_events:start_link'() -> {ok, pid()} | {error, term()}.
'riak_core_node_watcher_events:start_link'() -> error(overlay).

%% the result of gen_event:add_handler/3: ok, or what init/1 of the handler returned or failed with
-spec 'riak_core_node_watcher_events:add_handler'(core_handler(), list()) -> ok | {'EXIT', term()} | term().
'riak_core_node_watcher_events:add_handler'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:add_sup_handler'(core_handler(), list()) -> ok | {'EXIT', term()} | term().
'riak_core_node_watcher_events:add_sup_handler'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:add_guarded_handler'(core_handler(), list()) -> ok | {error, term()}.
'riak_core_node_watcher_events:add_guarded_handler'(_, _) -> error(overlay).

%% the handler is this module, its init/1 returns {ok, State} or fails in the callback
-spec 'riak_core_node_watcher_events:add_callback'(core_nwe_callback()) -> ok | {'EXIT', term()}.
'riak_core_node_watcher_events:add_callback'(_) -> error(overlay).

-spec 'riak_core_node_watcher_events:add_sup_callback'(core_nwe_callback()) -> ok | {'EXIT', term()}.
'riak_core_node_watcher_events:add_sup_callback'(_) -> error(overlay).

-spec 'riak_core_node_watcher_events:add_guarded_callback'(core_nwe_callback()) -> ok | {error, term()}.
'riak_core_node_watcher_events:add_guarded_callback'(_) -> error(overlay).

-spec 'riak_core_node_watcher_events:service_update'([atom()]) -> ok.
'riak_core_node_watcher_events:service_update'(_) -> error(overlay).

-spec 'riak_core_node_watcher_events:init'([core_nwe_callback()]) -> {ok, core_nwe_state()}.
'riak_core_node_watcher_events:init'(_) -> error(overlay).

-spec 'riak_core_node_watcher_events:handle_event'({service_update, [atom()]}, core_nwe_state()) ->
          {ok, core_nwe_state()}.
'riak_core_node_watcher_events:handle_event'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:handle_call'(term(), core_nwe_state()) -> {ok, ok, core_nwe_state()}.
'riak_core_node_watcher_events:handle_call'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:handle_info'(term(), core_nwe_state()) -> {ok, core_nwe_state()}.
'riak_core_node_watcher_events:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:terminate'(term(), core_nwe_state()) -> ok.
'riak_core_node_watcher_events:terminate'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher_events:code_change'(term(), core_nwe_state(), term()) -> {ok, core_nwe_state()}.
'riak_core_node_watcher_events:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_ring_events
%% ---------------------------------------------------------------------------------------------

%% a callback gets the new ring (at first the ring of the node), the result is dropped.
%% riak_core_ring_events does not mention riak_core_ring; the type is loaded with the spec of
%% riak_core_ring_manager:get_my_ring/0, which the module calls (see the notes).
-type core_re_callback() :: fun((riak_core_ring:riak_core_ring()) -> term()).

%% the record state: callback (no type)
-type core_re_state() :: {state, core_re_callback()}.

%% gen_event:start_link/1 has no ignore
-spec 'riak_core_ring_events:start_link'() -> {ok, pid()} | {error, term()}.
'riak_core_ring_events:start_link'() -> error(overlay).

%% the result of gen_event:add_handler/3: ok, or what init/1 of the handler returned or failed with
-spec 'riak_core_ring_events:add_handler'(core_handler(), list()) -> ok | {'EXIT', term()} | term().
'riak_core_ring_events:add_handler'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:add_sup_handler'(core_handler(), list()) -> ok | {'EXIT', term()} | term().
'riak_core_ring_events:add_sup_handler'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:add_guarded_handler'(core_handler(), list()) -> ok | {error, term()}.
'riak_core_ring_events:add_guarded_handler'(_, _) -> error(overlay).

%% the handler is this module, its init/1 returns {ok, State} or fails (no ring, or in the callback)
-spec 'riak_core_ring_events:add_callback'(core_re_callback()) -> ok | {'EXIT', term()}.
'riak_core_ring_events:add_callback'(_) -> error(overlay).

-spec 'riak_core_ring_events:add_sup_callback'(core_re_callback()) -> ok | {'EXIT', term()}.
'riak_core_ring_events:add_sup_callback'(_) -> error(overlay).

-spec 'riak_core_ring_events:add_guarded_callback'(core_re_callback()) -> ok | {error, term()}.
'riak_core_ring_events:add_guarded_callback'(_) -> error(overlay).

-spec 'riak_core_ring_events:force_update'() -> ok.
'riak_core_ring_events:force_update'() -> error(overlay).

-spec 'riak_core_ring_events:ring_update'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_events:ring_update'(_) -> error(overlay).

-spec 'riak_core_ring_events:force_sync_update'() -> ok.
'riak_core_ring_events:force_sync_update'() -> error(overlay).

-spec 'riak_core_ring_events:ring_sync_update'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_events:ring_sync_update'(_) -> error(overlay).

-spec 'riak_core_ring_events:init'([core_re_callback()]) -> {ok, core_re_state()}.
'riak_core_ring_events:init'(_) -> error(overlay).

-spec 'riak_core_ring_events:handle_event'({ring_update, riak_core_ring:riak_core_ring()}, core_re_state()) ->
          {ok, core_re_state()}.
'riak_core_ring_events:handle_event'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:handle_call'(term(), core_re_state()) -> {ok, ok, core_re_state()}.
'riak_core_ring_events:handle_call'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:handle_info'(term(), core_re_state()) -> {ok, core_re_state()}.
'riak_core_ring_events:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:terminate'(term(), core_re_state()) -> ok.
'riak_core_ring_events:terminate'(_, _) -> error(overlay).

-spec 'riak_core_ring_events:code_change'(term(), core_re_state(), term()) -> {ok, core_re_state()}.
'riak_core_ring_events:code_change'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_ring_handler
%% ---------------------------------------------------------------------------------------------

%% the record state has no fields
-type core_rh_state() :: {state}.

%% the index of a partition: chash:index_as_int(), but riak_core_ring_handler does not mention chash
-type core_rh_index() :: integer().

-spec 'riak_core_ring_handler:init'([]) -> {ok, core_rh_state()}.
'riak_core_ring_handler:init'(_) -> error(overlay).

-spec 'riak_core_ring_handler:handle_event'({ring_update, riak_core_ring:riak_core_ring()}, core_rh_state()) ->
          {ok, core_rh_state()}.
'riak_core_ring_handler:handle_event'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:handle_call'(term(), core_rh_state()) -> {ok, ok, core_rh_state()}.
'riak_core_ring_handler:handle_call'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:handle_info'(term(), core_rh_state()) -> {ok, core_rh_state()}.
'riak_core_ring_handler:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:terminate'(term(), core_rh_state()) -> ok.
'riak_core_ring_handler:terminate'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:code_change'(term(), core_rh_state(), term()) -> {ok, core_rh_state()}.
'riak_core_ring_handler:code_change'(_, _, _) -> error(overlay).

%% every branch ends in ok, also riak_core_ring_manager:refresh_my_ring/0
-spec 'riak_core_ring_handler:ensure_vnodes_started'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_handler:ensure_vnodes_started'(_) -> error(overlay).

-spec 'riak_core_ring_handler:maybe_shutdown'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_handler:maybe_shutdown'(_) -> error(overlay).

%% the result of riak_core_ring_manager:ring_trans/2
-spec 'riak_core_ring_handler:exit_ring_trans'() ->
          {ok, riak_core_ring:riak_core_ring()} | not_changed | {not_changed, term()}.
'riak_core_ring_handler:exit_ring_trans'() -> error(overlay).

%% the argument is riak_core:vnode_modules()
-spec 'riak_core_ring_handler:ready_to_exit'([core_app_mod()]) -> boolean().
'riak_core_ring_handler:ready_to_exit'(_) -> error(overlay).

%% the third argument collects the indices per vnode module, the result is all of them
-spec 'riak_core_ring_handler:ensure_vnodes_started'([core_app_mod()], riak_core_ring:riak_core_ring(),
                                                     [[core_rh_index()]]) ->
          [core_rh_index()].
'riak_core_ring_handler:ensure_vnodes_started'(_, _, _) -> error(overlay).

%% the indices of the vnodes that a spawned process starts
-spec 'riak_core_ring_handler:ensure_vnodes_started'(core_app_mod(), riak_core_ring:riak_core_ring()) ->
          [core_rh_index()].
'riak_core_ring_handler:ensure_vnodes_started'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:startable_vnodes'(module(), riak_core_ring:riak_core_ring()) -> [core_rh_index()].
'riak_core_ring_handler:startable_vnodes'(_, _) -> error(overlay).

-spec 'riak_core_ring_handler:maybe_start_vnode_proxies'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_handler:maybe_start_vnode_proxies'(_) -> error(overlay).

-spec 'riak_core_ring_handler:maybe_stop_vnode_proxies'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_handler:maybe_stop_vnode_proxies'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_node_watcher
%% ---------------------------------------------------------------------------------------------

%% A service is named by an atom (service_up/3, check_health/1), a node by node().

%% the record health_check. interval_tref, max_callback_failures and max_health_failures have no type
%% there: the timer of the next check, and the two limits that come from health_opts().
-type nw_health_check() :: {health_check,
                            waiting | checking | suspend,
                            {atom(), atom(), [any()]},
                            pid(),
                            pid() | undefined,
                            non_neg_integer(),
                            non_neg_integer(),
                            reference() | undefined,
                            timeout(),
                            non_neg_integer(),
                            non_neg_integer()}.

%% the record state, no field has a type there: status, services (an ordset), health_checks (an orddict
%% by service), healths_enabled, peers (an ordset), avsn, bcast_tref, bcast_mod.
-type nw_state() :: {state,
                     up | down,
                     [atom()],
                     [{atom(), nw_health_check()}],
                     boolean(),
                     [node()],
                     non_neg_integer(),
                     reference() | undefined,
                     {module(), atom()}}.

%% what the server tells the health check of a service: the three that arrive as messages of the
%% process (handle_check_msg/3), and the three it sends on its own
-type nw_check_msg() :: check_health | {result, pid(), boolean()} | {'EXIT', pid(), term()}.
-type nw_health_msg() :: nw_check_msg() | suspend | resume | remove.

%% what the health check answers: nothing to do, the service is up again, is down, forget the check
-type nw_health_reply() :: ok | up | down | remove.

-spec 'riak_core_node_watcher:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_node_watcher:start_link'() -> error(overlay).

-spec 'riak_core_node_watcher:service_up'(atom(), pid()) -> ok.
'riak_core_node_watcher:service_up'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:suspend_health_checks'() -> ok | already_disabled.
'riak_core_node_watcher:suspend_health_checks'() -> error(overlay).

-spec 'riak_core_node_watcher:resume_health_checks'() -> ok | already_enabled.
'riak_core_node_watcher:resume_health_checks'() -> error(overlay).

-spec 'riak_core_node_watcher:service_down'(atom()) -> ok.
'riak_core_node_watcher:service_down'(_) -> error(overlay).

%% the second argument: is the service taken down by its health check? (no caller in the package)
-spec 'riak_core_node_watcher:service_down'(atom(), boolean()) -> ok.
'riak_core_node_watcher:service_down'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:node_up'() -> ok.
'riak_core_node_watcher:node_up'() -> error(overlay).

-spec 'riak_core_node_watcher:node_down'() -> ok.
'riak_core_node_watcher:node_down'() -> error(overlay).

%% the services that are up on some node
-spec 'riak_core_node_watcher:services'() -> [atom()].
'riak_core_node_watcher:services'() -> error(overlay).

%% invalid_node: the node is not a member of the ring
-spec 'riak_core_node_watcher:services'(node()) -> [atom()] | invalid_node.
'riak_core_node_watcher:services'(_) -> error(overlay).

-spec 'riak_core_node_watcher:nodes'(atom()) -> [node()].
'riak_core_node_watcher:nodes'(_) -> error(overlay).

-spec 'riak_core_node_watcher:init'([]) -> {ok, nw_state()}.
'riak_core_node_watcher:init'(_) -> error(overlay).

%% the callback of a health check is typed as the record field that takes it: the third component is
%% the list of arguments (start_health_check/2 applies it), not the arity of the mfa() in service_up/4
-spec 'riak_core_node_watcher:handle_call'
        ({set_bcast_mod, module(), atom()} | get_avsn | {service_up, atom(), pid()} |
         {service_up, atom(), pid(), {atom(), atom(), [any()]}, riak_core_node_watcher:health_opts()} |
         {service_down, atom()} | {node_status, up | down} | services | suspend_healths | resume_healths,
         {pid(), term()}, nw_state()) ->
          {reply, ok | already_disabled | already_enabled | non_neg_integer() | [atom()], nw_state()}.
'riak_core_node_watcher:handle_call'(_, _, _) -> error(overlay).

%% up and down are the broadcasts of the node watchers of the other nodes
-spec 'riak_core_node_watcher:handle_cast'
        ({ring_update, riak_core_ring:riak_core_ring()} | {up, node(), [atom()]} | {down, node()} |
         {health_check_result, pid(), boolean()}, nw_state()) ->
          {noreply, nw_state()}.
'riak_core_node_watcher:handle_cast'(_, _) -> error(overlay).

%% 'DOWN' comes from the monitor of a service, 'EXIT' from the process of a health check,
%% gen_event_EXIT from the handler that watch_for_ring_events/0 has installed
-spec 'riak_core_node_watcher:handle_info'
        ({nodeup, node()} | {nodedown, node()} | {'DOWN', reference(), process, pid(), term()} |
         {'EXIT', pid(), term()} | {check_health, atom()} |
         {gen_event_EXIT, {riak_core_ring_events, reference()}, term()} | broadcast, nw_state()) ->
          {noreply, nw_state()}.
'riak_core_node_watcher:handle_info'(_, _) -> error(overlay).

%% the result is the one of broadcast/2, gen_server does not look at it
-spec 'riak_core_node_watcher:terminate'(term(), nw_state()) -> nw_state().
'riak_core_node_watcher:terminate'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:code_change'(term(), nw_state(), term()) -> {ok, nw_state()}.
'riak_core_node_watcher:code_change'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:check_node_valid'(node()) -> boolean().
'riak_core_node_watcher:check_node_valid'(_) -> error(overlay).

-spec 'riak_core_node_watcher:update_avsn'(nw_state()) -> nw_state().
'riak_core_node_watcher:update_avsn'(_) -> error(overlay).

%% gen_event:add_sup_handler/3: ok, or {'EXIT', _} if the init of the handler fails (no ring yet)
-spec 'riak_core_node_watcher:watch_for_ring_events'() -> ok | {'EXIT', term()}.
'riak_core_node_watcher:watch_for_ring_events'() -> error(overlay).

%% true is the result of erlang:demonitor/1
-spec 'riak_core_node_watcher:delete_service_mref'(atom()) -> ok | true.
'riak_core_node_watcher:delete_service_mref'(_) -> error(overlay).

-spec 'riak_core_node_watcher:broadcast'([node()], nw_state()) -> nw_state().
'riak_core_node_watcher:broadcast'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:schedule_broadcast'(nw_state()) -> nw_state().
'riak_core_node_watcher:schedule_broadcast'(_) -> error(overlay).

-spec 'riak_core_node_watcher:is_peer'(node(), nw_state()) -> boolean().
'riak_core_node_watcher:is_peer'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:is_node_up'(node()) -> boolean().
'riak_core_node_watcher:is_node_up'(_) -> error(overlay).

-spec 'riak_core_node_watcher:node_up'(node(), [atom()], nw_state()) -> nw_state().
'riak_core_node_watcher:node_up'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:node_down'(node(), nw_state()) -> ok.
'riak_core_node_watcher:node_down'(_, _) -> error(overlay).

%% the services that were up on the node
-spec 'riak_core_node_watcher:node_delete'(node()) -> [atom()].
'riak_core_node_watcher:node_delete'(_) -> error(overlay).

%% the second argument are the services that are up on the node, the result those that have changed
-spec 'riak_core_node_watcher:node_update'(node(), [atom()]) -> [atom()].
'riak_core_node_watcher:node_update'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:local_update'(nw_state()) -> nw_state().
'riak_core_node_watcher:local_update'(_) -> error(overlay).

-spec 'riak_core_node_watcher:local_delete'(nw_state()) -> nw_state().
'riak_core_node_watcher:local_delete'(_) -> error(overlay).

-spec 'riak_core_node_watcher:peers_update'([node()], nw_state()) -> nw_state().
'riak_core_node_watcher:peers_update'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:internal_delete'(node(), atom()) -> true.
'riak_core_node_watcher:internal_delete'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:internal_insert'(node(), atom()) -> true.
'riak_core_node_watcher:internal_insert'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:internal_get_services'(node()) -> [atom()].
'riak_core_node_watcher:internal_get_services'(_) -> error(overlay).

-spec 'riak_core_node_watcher:internal_get_nodes'(atom()) -> [node()].
'riak_core_node_watcher:internal_get_nodes'(_) -> error(overlay).

-spec 'riak_core_node_watcher:add_service'(atom(), pid(), nw_state()) -> nw_state().
'riak_core_node_watcher:add_service'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:drop_service'(atom(), nw_state()) -> nw_state().
'riak_core_node_watcher:drop_service'(_, _) -> error(overlay).

%% the service is undefined if the process dictionary knows no service for the pid of the message
-spec 'riak_core_node_watcher:handle_check_msg'(nw_check_msg(), atom() | undefined, nw_state()) -> nw_state().
'riak_core_node_watcher:handle_check_msg'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:handle_check_return'({nw_health_reply(), nw_health_check()}, atom(), nw_state()) ->
          nw_state().
'riak_core_node_watcher:handle_check_return'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:remove_health_check'(atom(), nw_state()) -> nw_state().
'riak_core_node_watcher:remove_health_check'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:health_fsm'(nw_health_msg(), atom(), nw_health_check()) ->
          {nw_health_reply(), nw_health_check()}.
'riak_core_node_watcher:health_fsm'(_, _, _) -> error(overlay).

%% the first argument is the state of the check, the second component of the result the next one
-spec 'riak_core_node_watcher:health_fsm'
        (waiting | checking | suspend, nw_health_msg(), atom(), nw_health_check()) ->
          {nw_health_reply(), waiting | checking | suspend, nw_health_check()}.
'riak_core_node_watcher:health_fsm'(_, _, _, _) -> error(overlay).

%% the result of a check, the health failures so far and their limit; the result has the new count
-spec 'riak_core_node_watcher:handle_fsm_exit'(boolean(), non_neg_integer(), non_neg_integer()) ->
          {up | ok | down, non_neg_integer()}.
'riak_core_node_watcher:handle_fsm_exit'(_, _, _) -> error(overlay).

-spec 'riak_core_node_watcher:start_health_check'(atom(), nw_health_check()) -> nw_health_check().
'riak_core_node_watcher:start_health_check'(_, _) -> error(overlay).

-spec 'riak_core_node_watcher:health_check_result'(pid(), boolean()) -> ok.
'riak_core_node_watcher:health_check_result'(_, _) -> error(overlay).

%% health failures, check interval, service; undefined: no automatic check (interval infinity)
-spec 'riak_core_node_watcher:next_health_tref'(non_neg_integer(), timeout(), atom()) -> reference() | undefined.
'riak_core_node_watcher:next_health_tref'(_, _, _) -> error(overlay).

%% only suspend and resume are sent to all checks, the answer to both is ok
-spec 'riak_core_node_watcher:all_health_fsms'(suspend | resume, [{atom(), nw_health_check()}]) ->
          [{atom(), nw_health_check()}].
'riak_core_node_watcher:all_health_fsms'(_, _) -> error(overlay).

%% health failures and the check interval in milliseconds (never infinity here)
-spec 'riak_core_node_watcher:determine_time'(non_neg_integer(), non_neg_integer()) -> non_neg_integer().
'riak_core_node_watcher:determine_time'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------
%% riak_core_ring_manager
%% ---------------------------------------------------------------------------------------------

%% the record state, no field has a type there: mode, raw_ring, ring_changed_time, inactivity_timer.
%% init/1 builds it with the mode only, so the ring and the time are undefined until set_ring/2 has run;
%% the timer is undefined when the ring has been promoted.
-type rm_state() :: {state,
                     live | test,
                     riak_core_ring:riak_core_ring() | undefined,
                     erlang:timestamp() | undefined,
                     reference() | undefined}.

%% {Epoch, Count}: the epoch counts the starts of the ring manager on this node, the count the rings
%% that were set in this epoch. {0, 0} without a ring manager.
-type rm_ring_id() :: {non_neg_integer(), non_neg_integer()}.

%% what the fun of ring_trans/2 may answer, and what ring_trans/2 makes of it: the reason of an ignore
%% is handed back as it is. (A helper type with a parameter that names a type of another module ends the
%% engine for every module that does not load that module, so the spec of ring_trans/2 spells this out
%% with a type variable for the reason.)
-type rm_trans_result() :: {new_ring, riak_core_ring:riak_core_ring()} |
                           {set_only, riak_core_ring:riak_core_ring()} |
                           {reconciled_ring, riak_core_ring:riak_core_ring()} |
                           ignore |
                           {ignore, term()}.
-type rm_trans_reply() :: {ok, riak_core_ring:riak_core_ring()} | not_changed | {not_changed, term()}.

%% chashbin:chashbin(). riak_core_ring_manager only calls chashbin and its callers do not all load it,
%% so the record is spelled out. The last field is erlang:tuple(node()) in chashbin.erl.
-type rm_chashbin() :: {chashbin, pos_integer(), <<_:_*176>>, tuple()}.

%% the error reasons of file:list_dir/1
-type rm_list_dir_error() :: file:posix() | badarg | {no_translation, binary()}.

%% the time stamp in the name of a ring file, as io_lib:fread/2 reads it:
%% [Year, Month, Day, Hour, Minute, Second]
-type rm_ts() :: [integer(), ...].

-spec 'riak_core_ring_manager:start_link'() -> {ok, pid()} | ignore | {error, term()}.
'riak_core_ring_manager:start_link'() -> error(overlay).

-spec 'riak_core_ring_manager:start_link'(test) -> {ok, pid()} | ignore | {error, term()}.
'riak_core_ring_manager:start_link'(_) -> error(overlay).

-spec 'riak_core_ring_manager:get_raw_ring'() -> {ok, riak_core_ring:riak_core_ring()}.
'riak_core_ring_manager:get_raw_ring'() -> error(overlay).

-spec 'riak_core_ring_manager:get_raw_ring_chashbin'() ->
          {ok, riak_core_ring:riak_core_ring(), rm_chashbin()}.
'riak_core_ring_manager:get_raw_ring_chashbin'() -> error(overlay).

-spec 'riak_core_ring_manager:refresh_my_ring'() -> ok.
'riak_core_ring_manager:refresh_my_ring'() -> error(overlay).

%% the name of a cluster is a term() for riak_core_ring:cluster_name/1, it is only compared
-spec 'riak_core_ring_manager:refresh_ring'(node(), term()) -> ok.
'riak_core_ring_manager:refresh_ring'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:set_my_ring'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_manager:set_my_ring'(_) -> error(overlay).

-spec 'riak_core_ring_manager:get_ring_id'() -> rm_ring_id().
'riak_core_ring_manager:get_ring_id'() -> error(overlay).

%% undefined: no such bucket in the ring. This is what the caller riak_core_bucket:get_bucket/1 expects;
%% the clause for a bucket with a type gives the result of that very function instead.
-spec 'riak_core_ring_manager:get_bucket_meta'(riak_core_bucket:bucket()) ->
          undefined | {ok, riak_core_bucket:properties()}.
'riak_core_ring_manager:get_bucket_meta'(_) -> error(overlay).

-spec 'riak_core_ring_manager:get_chash_bin'() -> {ok, rm_chashbin()} | {error, no_ring}.
'riak_core_ring_manager:get_chash_bin'() -> error(overlay).

-spec 'riak_core_ring_manager:write_ringfile'() -> ok.
'riak_core_ring_manager:write_ringfile'() -> error(overlay).

%% the second argument is handed to the fun as it is (the callers pass [], undefined, ok, a list with
%% a ring, a state record)
-spec 'riak_core_ring_manager:ring_trans'
        (fun((riak_core_ring:riak_core_ring(), Args) ->
                 {new_ring, riak_core_ring:riak_core_ring()} | {set_only, riak_core_ring:riak_core_ring()} |
                 {reconciled_ring, riak_core_ring:riak_core_ring()} | ignore | {ignore, Reason}),
         Args) ->
          {ok, riak_core_ring:riak_core_ring()} | not_changed | {not_changed, Reason}.
'riak_core_ring_manager:ring_trans'(_, _) -> error(overlay).

%% the name goes into the field clustername of the ring, a pair there
-spec 'riak_core_ring_manager:set_cluster_name'({term(), term()}) -> ok.
'riak_core_ring_manager:set_cluster_name'(_) -> error(overlay).

-spec 'riak_core_ring_manager:is_stable_ring'() -> boolean().
'riak_core_ring_manager:is_stable_ring'() -> error(overlay).

-spec 'riak_core_ring_manager:force_update'() -> ok.
'riak_core_ring_manager:force_update'() -> error(overlay).

%% nop: rings are not stored (ring_state_dir is "<nostore>")
-spec 'riak_core_ring_manager:do_write_ringfile'(riak_core_ring:riak_core_ring()) -> nop | ok | {error, term()}.
'riak_core_ring_manager:do_write_ringfile'(_) -> error(overlay).

%% the file name as riak_core_util:replace_file/2 wants it
-spec 'riak_core_ring_manager:do_write_ringfile'(riak_core_ring:riak_core_ring(), string()) ->
          ok | {error, term()}.
'riak_core_ring_manager:do_write_ringfile'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:find_latest_ringfile'() -> {ok, string()} | {error, not_found | rm_list_dir_error()}.
'riak_core_ring_manager:find_latest_ringfile'() -> error(overlay).

%% the error reasons are those of file:read_file/1
-spec 'riak_core_ring_manager:read_ringfile'(string()) ->
          riak_core_ring:riak_core_ring() | {error, file:posix() | badarg | terminated | system_limit}.
'riak_core_ring_manager:read_ringfile'(_) -> error(overlay).

-spec 'riak_core_ring_manager:prune_ringfiles'() -> ok | {error, rm_list_dir_error()}.
'riak_core_ring_manager:prune_ringfiles'() -> error(overlay).

-spec 'riak_core_ring_manager:init'([live | test, ...]) -> {ok, rm_state()}.
'riak_core_ring_manager:init'(_) -> error(overlay).

-spec 'riak_core_ring_manager:reload_ring'(live | test) -> riak_core_ring:riak_core_ring().
'riak_core_ring_manager:reload_ring'(_) -> error(overlay).

%% From is undefined when handle_cast/2 calls this function for refresh_my_ring.
%% The fun and its argument are those of ring_trans/2, the argument can be any term here.
-spec 'riak_core_ring_manager:handle_call'
        (get_raw_ring | get_raw_ring_chashbin | {set_my_ring, riak_core_ring:riak_core_ring()} | refresh_my_ring |
         {ring_trans, fun((riak_core_ring:riak_core_ring(), term()) -> rm_trans_result()), term()} |
         {set_cluster_name, {term(), term()}} | is_stable_ring | stop,
         {pid(), term()} | undefined, rm_state()) ->
          {reply,
           {ok, riak_core_ring:riak_core_ring()} | {ok, riak_core_ring:riak_core_ring(), rm_chashbin()} |
           ok | rm_trans_reply() | boolean(),
           rm_state()} |
          {stop, normal, ok, rm_state()}.
'riak_core_ring_manager:handle_call'(_, _, _) -> error(overlay).

%% the state is never the atom test that the first clause for write_ringfile matches
-spec 'riak_core_ring_manager:handle_cast'
        ({refresh_my_ring, term()} | refresh_my_ring | write_ringfile, rm_state()) ->
          {noreply, rm_state()}.
'riak_core_ring_manager:handle_cast'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:handle_info'(term(), rm_state()) -> {noreply, rm_state()}.
'riak_core_ring_manager:handle_info'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:terminate'(term(), rm_state()) -> ok.
'riak_core_ring_manager:terminate'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:code_change'(term(), rm_state(), term()) -> {ok, rm_state()}.
'riak_core_ring_manager:code_change'(_, _, _) -> error(overlay).

%% compared with "<nostore>" and used as a prefix of the file names
-spec 'riak_core_ring_manager:ring_dir'() -> string().
'riak_core_ring_manager:ring_dir'() -> error(overlay).

%% the time stamps to keep; there is no clause for the empty list
-spec 'riak_core_ring_manager:prune_list'([rm_ts(), ...]) -> [rm_ts()].
'riak_core_ring_manager:prune_list'(_) -> error(overlay).

%% the first time stamp of the list that differs from the given one in the component N
-spec 'riak_core_ring_manager:back'(pos_integer(), rm_ts(), [rm_ts()]) -> [rm_ts()].
'riak_core_ring_manager:back'(_, _, _) -> error(overlay).

%% the fixups are riak_core:bucket_fixups(), pairs of an application and its fixup module;
%% riak_core_bucket_props:append_defaults/1 runs them on the default properties under the name default
-spec 'riak_core_ring_manager:run_fixups'([{atom(), module()}], riak_core_bucket:bucket() | default,
                                          riak_core_bucket:properties()) ->
          riak_core_bucket:properties().
'riak_core_ring_manager:run_fixups'(_, _, _) -> error(overlay).

-spec 'riak_core_ring_manager:set_ring'(riak_core_ring:riak_core_ring(), rm_state()) -> rm_state().
'riak_core_ring_manager:set_ring'(_, _) -> error(overlay).

%% the duration is the time of erlang:send_after/3
-spec 'riak_core_ring_manager:maybe_set_timer'(non_neg_integer(), rm_state()) -> rm_state().
'riak_core_ring_manager:maybe_set_timer'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:set_timer'(non_neg_integer(), rm_state()) -> rm_state().
'riak_core_ring_manager:set_timer'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:setup_ets'(live | test) -> ok.
'riak_core_ring_manager:setup_ets'(_) -> error(overlay).

-spec 'riak_core_ring_manager:cleanup_ets'(test) -> true.
'riak_core_ring_manager:cleanup_ets'(_) -> error(overlay).

-spec 'riak_core_ring_manager:reset_ring_id'() -> rm_ring_id().
'riak_core_ring_manager:reset_ring_id'() -> error(overlay).

-spec 'riak_core_ring_manager:set_ring_global'(riak_core_ring:riak_core_ring()) -> ok.
'riak_core_ring_manager:set_ring_global'(_) -> error(overlay).

-spec 'riak_core_ring_manager:promote_ring'() -> ok.
'riak_core_ring_manager:promote_ring'() -> error(overlay).

-spec 'riak_core_ring_manager:prune_write_notify_ring'(riak_core_ring:riak_core_ring(), rm_state()) -> rm_state().
'riak_core_ring_manager:prune_write_notify_ring'(_, _) -> error(overlay).

-spec 'riak_core_ring_manager:prune_write_ring'(riak_core_ring:riak_core_ring(), rm_state()) -> rm_state().
'riak_core_ring_manager:prune_write_ring'(_, _) -> error(overlay).

%% is the ring unchanged for the promote timeout, and the milliseconds since the last change
-spec 'riak_core_ring_manager:is_stable_ring'(rm_state()) -> {boolean(), non_neg_integer()}.
'riak_core_ring_manager:is_stable_ring'(_) -> error(overlay).
