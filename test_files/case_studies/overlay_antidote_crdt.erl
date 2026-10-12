%% Specs for the functions of the antidote_crdt case study that have none in the source.
%% Each spec uses the types of the module of its function, as a spec in the source would.
-module(overlay_antidote_crdt).
-compile([export_all, nowarn_export_all]).

%% --- antidote_crdt_counter_b ---

-spec 'antidote_crdt_counter_b:generate_downstream_check'(
        {increment | decrement, pos_integer()} | {transfer, pos_integer(), antidote_crdt_counter_b:id()},
        antidote_crdt_counter_b:id(), antidote_crdt_counter_b:antidote_crdt_counter_b(), pos_integer()) ->
          {ok, antidote_crdt_counter_b:antidote_crdt_counter_b_effect()} | {error, no_permissions}.
'antidote_crdt_counter_b:generate_downstream_check'(_, _, _, _) -> error(overlay).

%% --- antidote_crdt_counter_fat ---

-spec 'antidote_crdt_counter_fat:apply_downstreams'([antidote_crdt_counter_fat:uniqueToken()], antidote_crdt_counter_fat:state()) ->
          antidote_crdt_counter_fat:state().
'antidote_crdt_counter_fat:apply_downstreams'(_, _) -> error(overlay).

-spec 'antidote_crdt_counter_fat:is_bottom'(antidote_crdt_counter_fat:state()) -> boolean().
'antidote_crdt_counter_fat:is_bottom'(_) -> error(overlay).

-spec 'antidote_crdt_counter_fat:require_state_downstream'(antidote_crdt_counter_fat:op()) -> boolean().
'antidote_crdt_counter_fat:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_counter_pn ---

-spec 'antidote_crdt_counter_pn:new'() -> antidote_crdt_counter_pn:state().
'antidote_crdt_counter_pn:new'() -> error(overlay).

-spec 'antidote_crdt_counter_pn:from_binary'(binary()) -> {ok, antidote_crdt_counter_pn:state()}.
'antidote_crdt_counter_pn:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_counter_pn:require_state_downstream'(antidote_crdt_counter_pn:op()) -> boolean().
'antidote_crdt_counter_pn:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_flag_dw ---

-spec 'antidote_crdt_flag_dw:from_binary'(antidote_crdt_flag_helper:binary_flag()) -> {ok, antidote_crdt_flag_dw:flag_dw()}.
'antidote_crdt_flag_dw:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_flag_dw:is_operation'(term()) -> boolean().
'antidote_crdt_flag_dw:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_flag_dw:is_bottom'(antidote_crdt_flag_dw:flag_dw()) -> boolean().
'antidote_crdt_flag_dw:is_bottom'(_) -> error(overlay).

-spec 'antidote_crdt_flag_dw:require_state_downstream'(antidote_crdt_flag_helper:op()) -> boolean().
'antidote_crdt_flag_dw:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_flag_ew ---

-spec 'antidote_crdt_flag_ew:from_binary'(antidote_crdt_flag_helper:binary_flag()) -> {ok, antidote_crdt_flag_ew:flag_ew()}.
'antidote_crdt_flag_ew:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_flag_ew:is_operation'(term()) -> boolean().
'antidote_crdt_flag_ew:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_flag_ew:is_bottom'(antidote_crdt_flag_ew:flag_ew()) -> boolean().
'antidote_crdt_flag_ew:is_bottom'(_) -> error(overlay).

-spec 'antidote_crdt_flag_ew:require_state_downstream'(antidote_crdt_flag_helper:op()) -> boolean().
'antidote_crdt_flag_ew:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_flag_helper ---

-spec 'antidote_crdt_flag_helper:unique'() -> antidote_crdt_flag_helper:token().
'antidote_crdt_flag_helper:unique'() -> error(overlay).

%% the state of a flag differs between flag_ew and flag_dw
-spec 'antidote_crdt_flag_helper:from_binary'(antidote_crdt_flag_helper:binary_flag()) -> {ok, term()}.
'antidote_crdt_flag_helper:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_flag_helper:is_operation'(term()) -> boolean().
'antidote_crdt_flag_helper:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_flag_helper:require_state_downstream'(antidote_crdt_flag_helper:op()) -> boolean().
'antidote_crdt_flag_helper:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_map_go ---

%% the effect of a list of updates is a list of effects: downstream/2 builds it from its own results
-spec 'antidote_crdt_map_go:apply_ops'([antidote_crdt_map_go:antidote_crdt_map_go_effect()], antidote_crdt_map_go:antidote_crdt_map_go()) ->
          {ok, antidote_crdt_map_go:antidote_crdt_map_go()}.
'antidote_crdt_map_go:apply_ops'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_go:equal'(antidote_crdt_map_go:antidote_crdt_map_go(), antidote_crdt_map_go:antidote_crdt_map_go()) -> boolean().
'antidote_crdt_map_go:equal'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_go:to_binary'(antidote_crdt_map_go:antidote_crdt_map_go()) -> binary().
'antidote_crdt_map_go:to_binary'(_) -> error(overlay).

-spec 'antidote_crdt_map_go:from_binary'(binary()) -> {ok, antidote_crdt_map_go:antidote_crdt_map_go()}.
'antidote_crdt_map_go:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_map_go:is_operation'(term()) -> boolean().
'antidote_crdt_map_go:is_operation'(_) -> error(overlay).

%% --- antidote_crdt_map_rr ---

-spec 'antidote_crdt_map_rr:update_entry'(antidote_crdt_map_rr:nested_downstream(), antidote_crdt_map_rr:state()) ->
          antidote_crdt_map_rr:state().
'antidote_crdt_map_rr:update_entry'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_rr:remove_entry'(antidote_crdt_map_rr:nested_downstream(), antidote_crdt_map_rr:state()) ->
          antidote_crdt_map_rr:state().
'antidote_crdt_map_rr:remove_entry'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_rr:remove_obsolete'(antidote_crdt_map_rr:typedKey(), NestedState :: term(), antidote_crdt_map_rr:state()) ->
          antidote_crdt_map_rr:state().
'antidote_crdt_map_rr:remove_obsolete'(_, _, _) -> error(overlay).

%% the type of a key is an atom() throughout this module, see typedKey()
-spec 'antidote_crdt_map_rr:is_bottom'(Type :: atom(), NestedState :: term()) -> boolean().
'antidote_crdt_map_rr:is_bottom'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_rr:equal'(antidote_crdt_map_rr:state(), antidote_crdt_map_rr:state()) -> boolean().
'antidote_crdt_map_rr:equal'(_, _) -> error(overlay).

-spec 'antidote_crdt_map_rr:to_binary'(antidote_crdt_map_rr:state()) -> binary().
'antidote_crdt_map_rr:to_binary'(_) -> error(overlay).

-spec 'antidote_crdt_map_rr:from_binary'(binary()) -> {ok, antidote_crdt_map_rr:state()}.
'antidote_crdt_map_rr:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_map_rr:is_operation'(term()) -> boolean().
'antidote_crdt_map_rr:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_map_rr:is_bottom'(antidote_crdt_map_rr:state()) -> boolean().
'antidote_crdt_map_rr:is_bottom'(_) -> error(overlay).

%% --- antidote_crdt_register_lww ---

-spec 'antidote_crdt_register_lww:new'() -> antidote_crdt_register_lww:antidote_crdt_register_lww().
'antidote_crdt_register_lww:new'() -> error(overlay).

-spec 'antidote_crdt_register_lww:value'(antidote_crdt_register_lww:antidote_crdt_register_lww()) -> term().
'antidote_crdt_register_lww:value'(_) -> error(overlay).

-spec 'antidote_crdt_register_lww:make_micro_epoch'() -> non_neg_integer().
'antidote_crdt_register_lww:make_micro_epoch'() -> error(overlay).

%% the effect of an assignment is the state it leads to
-spec 'antidote_crdt_register_lww:update'(antidote_crdt_register_lww:antidote_crdt_register_lww(),
                                          antidote_crdt_register_lww:antidote_crdt_register_lww()) ->
          {ok, antidote_crdt_register_lww:antidote_crdt_register_lww()}.
'antidote_crdt_register_lww:update'(_, _) -> error(overlay).

-spec 'antidote_crdt_register_lww:require_state_downstream'(antidote_crdt_register_lww:antidote_crdt_register_lww_op()) -> boolean().
'antidote_crdt_register_lww:require_state_downstream'(_) -> error(overlay).

-spec 'antidote_crdt_register_lww:is_operation'(term()) -> boolean().
'antidote_crdt_register_lww:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_register_lww:equal'(antidote_crdt_register_lww:antidote_crdt_register_lww(),
                                         antidote_crdt_register_lww:antidote_crdt_register_lww()) -> boolean().
'antidote_crdt_register_lww:equal'(_, _) -> error(overlay).

-spec 'antidote_crdt_register_lww:to_binary'(antidote_crdt_register_lww:antidote_crdt_register_lww()) -> binary().
'antidote_crdt_register_lww:to_binary'(_) -> error(overlay).

-spec 'antidote_crdt_register_lww:from_binary'(binary()) -> {ok, antidote_crdt_register_lww:antidote_crdt_register_lww()}.
'antidote_crdt_register_lww:from_binary'(_) -> error(overlay).

%% --- antidote_crdt_register_mv ---

-spec 'antidote_crdt_register_mv:insert_sorted'({term(), antidote_crdt_register_mv:uniqueToken()},
                                                antidote_crdt_register_mv:antidote_crdt_register_mv()) ->
          antidote_crdt_register_mv:antidote_crdt_register_mv().
'antidote_crdt_register_mv:insert_sorted'(_, _) -> error(overlay).

-spec 'antidote_crdt_register_mv:require_state_downstream'(antidote_crdt_register_mv:antidote_crdt_register_mv_op()) -> boolean().
'antidote_crdt_register_mv:require_state_downstream'(_) -> error(overlay).

-spec 'antidote_crdt_register_mv:is_bottom'(antidote_crdt_register_mv:antidote_crdt_register_mv()) -> boolean().
'antidote_crdt_register_mv:is_bottom'(_) -> error(overlay).

%% --- antidote_crdt_secure_counter_pn ---

-spec 'antidote_crdt_secure_counter_pn:require_state_downstream'(antidote_crdt_secure_counter_pn:op()) -> boolean().
'antidote_crdt_secure_counter_pn:require_state_downstream'(_) -> error(overlay).

%% --- antidote_crdt_set_aw ---

-spec 'antidote_crdt_set_aw:from_binary'(antidote_crdt_set_aw:binary_antidote_crdt_set_aw()) ->
          {ok, antidote_crdt_set_aw:antidote_crdt_set_aw()}.
'antidote_crdt_set_aw:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_set_aw:create_downstreams'(
        fun((antidote_crdt_set_aw:member(), antidote_crdt_set_aw:tokens()) ->
                   {antidote_crdt_set_aw:member(), antidote_crdt_set_aw:tokens(), antidote_crdt_set_aw:tokens()}),
        [antidote_crdt_set_aw:member()], antidote_crdt_set_aw:antidote_crdt_set_aw(), antidote_crdt_set_aw:downstream_op()) ->
          antidote_crdt_set_aw:downstream_op().
'antidote_crdt_set_aw:create_downstreams'(_, _, _, _) -> error(overlay).

-spec 'antidote_crdt_set_aw:apply_downstreams'(antidote_crdt_set_aw:downstream_op(), antidote_crdt_set_aw:antidote_crdt_set_aw()) ->
          antidote_crdt_set_aw:antidote_crdt_set_aw().
'antidote_crdt_set_aw:apply_downstreams'(_, _) -> error(overlay).

%% no entry or the one of the element
-spec 'antidote_crdt_set_aw:apply_downstream'(antidote_crdt_set_aw:member(), antidote_crdt_set_aw:tokens(),
                                              antidote_crdt_set_aw:tokens(), antidote_crdt_set_aw:tokens()) ->
          antidote_crdt_set_aw:antidote_crdt_set_aw().
'antidote_crdt_set_aw:apply_downstream'(_, _, _, _) -> error(overlay).

-spec 'antidote_crdt_set_aw:is_operation'(term()) -> boolean().
'antidote_crdt_set_aw:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_set_aw:require_state_downstream'(antidote_crdt_set_aw:antidote_crdt_set_aw_op()) -> boolean().
'antidote_crdt_set_aw:require_state_downstream'(_) -> error(overlay).

-spec 'antidote_crdt_set_aw:is_bottom'(antidote_crdt_set_aw:antidote_crdt_set_aw()) -> boolean().
'antidote_crdt_set_aw:is_bottom'(_) -> error(overlay).

%% --- antidote_crdt_set_go ---

-spec 'antidote_crdt_set_go:new'() -> antidote_crdt_set_go:antidote_crdt_set_go().
'antidote_crdt_set_go:new'() -> error(overlay).

-spec 'antidote_crdt_set_go:value'(antidote_crdt_set_go:antidote_crdt_set_go()) -> [antidote_crdt_set_go:member()].
'antidote_crdt_set_go:value'(_) -> error(overlay).

-spec 'antidote_crdt_set_go:update'(antidote_crdt_set_go:antidote_crdt_set_go_effect(), antidote_crdt_set_go:antidote_crdt_set_go()) ->
          {ok, antidote_crdt_set_go:antidote_crdt_set_go()}.
'antidote_crdt_set_go:update'(_, _) -> error(overlay).

-spec 'antidote_crdt_set_go:require_state_downstream'(antidote_crdt_set_go:antidote_crdt_set_go_op()) -> boolean().
'antidote_crdt_set_go:require_state_downstream'(_) -> error(overlay).

-spec 'antidote_crdt_set_go:is_operation'(term()) -> boolean().
'antidote_crdt_set_go:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_set_go:equal'(antidote_crdt_set_go:antidote_crdt_set_go(), antidote_crdt_set_go:antidote_crdt_set_go()) -> boolean().
'antidote_crdt_set_go:equal'(_, _) -> error(overlay).

-spec 'antidote_crdt_set_go:to_binary'(antidote_crdt_set_go:antidote_crdt_set_go()) -> binary().
'antidote_crdt_set_go:to_binary'(_) -> error(overlay).

-spec 'antidote_crdt_set_go:from_binary'(binary()) -> {ok, antidote_crdt_set_go:antidote_crdt_set_go()}.
'antidote_crdt_set_go:from_binary'(_) -> error(overlay).

%% --- antidote_crdt_set_rw ---

-spec 'antidote_crdt_set_rw:create_downstreams'(
        fun((antidote_crdt_set_rw:member(), antidote_crdt_set_rw:tokens()) ->
                   {antidote_crdt_set_rw:member(), antidote_crdt_set_rw:tokens(), antidote_crdt_set_rw:tokens(),
                    antidote_crdt_set_rw:tokens()}),
        [antidote_crdt_set_rw:member()], antidote_crdt_set_rw:antidote_crdt_set_rw(), antidote_crdt_set_rw:downstream_op()) ->
          antidote_crdt_set_rw:downstream_op().
'antidote_crdt_set_rw:create_downstreams'(_, _, _, _) -> error(overlay).

-spec 'antidote_crdt_set_rw:unique'() -> antidote_crdt_set_rw:token().
'antidote_crdt_set_rw:unique'() -> error(overlay).

-spec 'antidote_crdt_set_rw:apply_downstreams'(antidote_crdt_set_rw:downstream_op(), antidote_crdt_set_rw:antidote_crdt_set_rw()) ->
          antidote_crdt_set_rw:antidote_crdt_set_rw().
'antidote_crdt_set_rw:apply_downstreams'(_, _) -> error(overlay).

%% the entry of the element
-spec 'antidote_crdt_set_rw:apply_downstream'(antidote_crdt_set_rw:member(), antidote_crdt_set_rw:tokens(),
                                              antidote_crdt_set_rw:tokens(), antidote_crdt_set_rw:tokens(),
                                              antidote_crdt_set_rw:tokens(), antidote_crdt_set_rw:tokens()) ->
          {antidote_crdt_set_rw:member(), {antidote_crdt_set_rw:tokens(), antidote_crdt_set_rw:tokens()}}.
'antidote_crdt_set_rw:apply_downstream'(_, _, _, _, _, _) -> error(overlay).

-spec 'antidote_crdt_set_rw:from_binary'(antidote_crdt_set_rw:binary_antidote_crdt_set_rw()) ->
          {ok, antidote_crdt_set_rw:antidote_crdt_set_rw()}.
'antidote_crdt_set_rw:from_binary'(_) -> error(overlay).

-spec 'antidote_crdt_set_rw:is_operation'(term()) -> boolean().
'antidote_crdt_set_rw:is_operation'(_) -> error(overlay).

-spec 'antidote_crdt_set_rw:is_bottom'(antidote_crdt_set_rw:antidote_crdt_set_rw()) -> boolean().
'antidote_crdt_set_rw:is_bottom'(_) -> error(overlay).

-spec 'antidote_crdt_set_rw:require_state_downstream'(antidote_crdt_set_rw:antidote_crdt_set_rw_op()) -> boolean().
'antidote_crdt_set_rw:require_state_downstream'(_) -> error(overlay).
