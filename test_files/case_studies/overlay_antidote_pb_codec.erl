%% Specs for the functions of antidote_pb_codec that have none in the source.
%% Encoding takes the types of the module (request(), response(), update(), ...). Decoding gives them
%% back where a message() is made of the result (a bound object, an update, a read result); the
%% operation of an update, a Param :: any() of update(), is given as the generated records declare it:
%% iodata() for a binary.
-module(overlay_antidote_pb_codec).
-compile([export_all, nowarn_export_all]).

%% An operation on a CRDT and its parameter, as in update().
-type op() :: {atom(), any()}.
%% A key of a map and its CRDT type, as an update names it: encode_type/1 takes any atom and fails
%% for one that is no CRDT type.
-type map_key() :: {binary(), atom()}.
%% A key of a map as decode_map_key/1 gives it, and as a read result has it.
-type dec_map_key() :: {binary(), antidote_pb_codec:crdt_type()}.
%% An entry of a map that was read: the value is not tagged.
-type map_entry() :: {dec_map_key(), antidote_pb_codec:read_value()}.
%% The tag that encode_crdt_type/1 gives a read result.
-type tag() :: reg | mvreg | counter | set | map | flag.
-type dec_update() :: {atom(), term()} | [].

%% --- message names and codes ---

-spec 'antidote_pb_codec:message_type_to_code'(atom()) -> byte().
'antidote_pb_codec:message_type_to_code'(_) -> error(overlay).

-spec 'antidote_pb_codec:message_code_to_type'(integer()) -> atom().
'antidote_pb_codec:message_code_to_type'(_) -> error(overlay).

%% --- error codes ---

-spec 'antidote_pb_codec:encode_error_code'(antidote_pb_codec:error_code()) -> non_neg_integer().
'antidote_pb_codec:encode_error_code'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_error_code'(non_neg_integer()) -> antidote_pb_codec:error_code().
'antidote_pb_codec:decode_error_code'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_error_resp'(antidote_pb_codec:error_code(), binary()) -> antidote_pb:'ApbErrorResp'().
'antidote_pb_codec:encode_error_resp'(_, _) -> error(overlay).

%% --- transactions ---

-spec 'antidote_pb_codec:encode_start_transaction'(Clock :: binary() | undefined, Properties :: list()) -> antidote_pb:'ApbStartTransaction'().
'antidote_pb_codec:encode_start_transaction'(_, _) -> error(overlay).

-spec 'antidote_pb_codec:encode_commit_transaction'(TxId :: binary()) -> antidote_pb:'ApbCommitTransaction'().
'antidote_pb_codec:encode_commit_transaction'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_abort_transaction'(TxId :: binary()) -> antidote_pb:'ApbAbortTransaction'().
'antidote_pb_codec:encode_abort_transaction'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_txn_properties'(Properties :: list()) -> antidote_pb:'ApbTxnProperties'().
'antidote_pb_codec:encode_txn_properties'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_txn_properties'(antidote_pb:'ApbTxnProperties'() | undefined) ->
          [{shared_locks | exclusive_locks, [binary()]}].
'antidote_pb_codec:decode_txn_properties'(_) -> error(overlay).

%% --- bound objects ---

-spec 'antidote_pb_codec:encode_bound_object'(antidote_pb_codec:bound_object()) -> antidote_pb:'ApbBoundObject'().
'antidote_pb_codec:encode_bound_object'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_bound_object'(Key :: binary(), Type :: antidote_pb_codec:crdt_type(), Bucket :: binary()) -> antidote_pb:'ApbBoundObject'().
'antidote_pb_codec:encode_bound_object'(_, _, _) -> error(overlay).

-spec 'antidote_pb_codec:decode_bound_object'(antidote_pb:'ApbBoundObject'()) -> antidote_pb_codec:bound_object().
'antidote_pb_codec:decode_bound_object'(_) -> error(overlay).

%% --- updates ---

-spec 'antidote_pb_codec:encode_static_update_objects'(Clock :: binary() | undefined, Properties :: list(), [antidote_pb_codec:update()]) ->
          antidote_pb:'ApbStaticUpdateObjects'().
'antidote_pb_codec:encode_static_update_objects'(_, _, _) -> error(overlay).

-spec 'antidote_pb_codec:decode_update_op'(antidote_pb:'ApbUpdateOp'()) -> antidote_pb_codec:update().
'antidote_pb_codec:decode_update_op'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_update_op'(antidote_pb_codec:update()) -> antidote_pb:'ApbUpdateOp'().
'antidote_pb_codec:encode_update_op'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_update_op'(antidote_pb_codec:bound_object(), Op :: atom(), Param :: any()) -> antidote_pb:'ApbUpdateOp'().
'antidote_pb_codec:encode_update_op'(_, _, _) -> error(overlay).

-spec 'antidote_pb_codec:encode_update_objects'([antidote_pb_codec:update()], TxId :: binary()) -> antidote_pb:'ApbUpdateObjects'().
'antidote_pb_codec:encode_update_objects'(_, _) -> error(overlay).

%% --- responses ---

-spec 'antidote_pb_codec:encode_start_transaction_response'({ok, TxId :: binary()} | {error, antidote_pb_codec:error_code()}) ->
          antidote_pb:'ApbStartTransactionResp'().
'antidote_pb_codec:encode_start_transaction_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_operation_response'(ok | {error, antidote_pb_codec:error_code()}) -> antidote_pb:'ApbOperationResp'().
'antidote_pb_codec:encode_operation_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_commit_response'({ok, CommitTime :: binary()} | {error, antidote_pb_codec:error_code()}) ->
          antidote_pb:'ApbCommitResp'().
'antidote_pb_codec:encode_commit_response'(_) -> error(overlay).

%% --- reading objects ---

-spec 'antidote_pb_codec:encode_static_read_objects_response'({[antidote_pb_codec:read_result()], CommitTime :: binary()}) ->
          antidote_pb:'ApbStaticReadObjectsResp'().
'antidote_pb_codec:encode_static_read_objects_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_read_objects_response'({ok, [antidote_pb_codec:read_result()]} | {error, antidote_pb_codec:error_code()}) ->
          antidote_pb:'ApbReadObjectsResp'().
'antidote_pb_codec:encode_read_objects_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_validate_or_read_objects_response'(
        {ok, {[antidote_pb_codec:read_result()], Tokens :: [binary()]}} | {error, antidote_pb_codec:error_code()}) ->
          antidote_pb:'ApbValidateOrReadObjectsResp'().
'antidote_pb_codec:encode_validate_or_read_objects_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_static_read_objects'(Clock :: binary() | undefined, Properties :: list(), [antidote_pb_codec:bound_object()]) ->
          antidote_pb:'ApbStaticReadObjects'().
'antidote_pb_codec:encode_static_read_objects'(_, _, _) -> error(overlay).

-spec 'antidote_pb_codec:encode_read_objects'([antidote_pb_codec:bound_object()], TxId :: binary()) -> antidote_pb:'ApbReadObjects'().
'antidote_pb_codec:encode_read_objects'(_, _) -> error(overlay).

-spec 'antidote_pb_codec:encode_validate_or_read_objects'([antidote_pb_codec:bound_object()], Tokens :: [binary()], TxId :: binary()) ->
          antidote_pb:'ApbValidateOrReadObjects'().
'antidote_pb_codec:encode_validate_or_read_objects'(_, _, _) -> error(overlay).

%% --- CRDT types ---

-spec 'antidote_pb_codec:encode_type'(atom()) -> antidote_pb:'CRDT_type'().
'antidote_pb_codec:encode_type'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_type'(antidote_pb:'CRDT_type'() | integer()) -> antidote_pb_codec:crdt_type().
'antidote_pb_codec:decode_type'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_crdt_type'(antidote_pb_codec:crdt_type()) -> tag().
'antidote_pb_codec:encode_crdt_type'(_) -> error(overlay).

%% --- CRDT operations ---

-spec 'antidote_pb_codec:encode_update_operation'(Type :: atom(), op()) -> antidote_pb:'ApbUpdateOperation'().
'antidote_pb_codec:encode_update_operation'(_, _) -> error(overlay).

%% [] comes from decode_set_update/1
-spec 'antidote_pb_codec:decode_update_operation'(antidote_pb:'ApbUpdateOperation'()) -> dec_update().
'antidote_pb_codec:decode_update_operation'(_) -> error(overlay).

%% the type of the value depends on the tag
-spec 'antidote_pb_codec:encode_read_object_resp'(tag(), Value :: antidote_pb_codec:read_value()) ->
          antidote_pb:'ApbReadObjectResp'().
'antidote_pb_codec:encode_read_object_resp'(_, _) -> error(overlay).

-spec 'antidote_pb_codec:decode_read_object_resp'(antidote_pb:'ApbReadObjectResp'()) -> antidote_pb_codec:read_result().
'antidote_pb_codec:decode_read_object_resp'(_) -> error(overlay).

%% --- set updates ---

-spec 'antidote_pb_codec:encode_set_update'({add | remove, binary()} | {add_all | remove_all, [binary()]}) -> antidote_pb:'ApbSetUpdate'().
'antidote_pb_codec:encode_set_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_set_update'(antidote_pb:'ApbSetUpdate'()) ->
          [] | {add | remove, iodata()} | {add_all | remove_all, [iodata()]}.
'antidote_pb_codec:decode_set_update'(_) -> error(overlay).

%% --- counter updates ---

-spec 'antidote_pb_codec:encode_counter_update'({increment | decrement, integer()}) -> antidote_pb:'ApbCounterUpdate'().
'antidote_pb_codec:encode_counter_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_counter_update'(antidote_pb:'ApbCounterUpdate'()) -> {increment, integer()}.
'antidote_pb_codec:decode_counter_update'(_) -> error(overlay).

%% --- register updates ---

-spec 'antidote_pb_codec:encode_reg_update'({assign, binary()}) -> antidote_pb:'ApbRegUpdate'().
'antidote_pb_codec:encode_reg_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_reg_update'(antidote_pb:'ApbRegUpdate'()) -> {assign, iodata()}.
'antidote_pb_codec:decode_reg_update'(_) -> error(overlay).

%% --- flag updates ---

-spec 'antidote_pb_codec:encode_flag_update'({enable, {}} | {disable, {}}) -> antidote_pb:'ApbFlagUpdate'().
'antidote_pb_codec:encode_flag_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_flag_update'(antidote_pb:'ApbFlagUpdate'()) -> {enable, {}} | {disable, {}}.
'antidote_pb_codec:decode_flag_update'(_) -> error(overlay).

%% --- map updates ---

-spec 'antidote_pb_codec:encode_map_update'(
        {update, {map_key(), op()} | [{map_key(), op()}]} | {remove, map_key() | [map_key()]}
      | {batch, {[{map_key(), op()}], [map_key()]}}) ->
          antidote_pb:'ApbMapUpdate'().
'antidote_pb_codec:encode_map_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_map_update'(antidote_pb:'ApbMapUpdate'()) ->
          {update, {dec_map_key(), dec_update()} | [{dec_map_key(), dec_update()}]} | {remove, dec_map_key() | [dec_map_key()]}
        | {batch, {[{dec_map_key(), dec_update()}], [dec_map_key()]}}.
'antidote_pb_codec:decode_map_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_map_nested_update'({map_key(), op()}) -> antidote_pb:'ApbMapNestedUpdate'().
'antidote_pb_codec:encode_map_nested_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_map_nested_update'(antidote_pb:'ApbMapNestedUpdate'()) -> {dec_map_key(), dec_update()}.
'antidote_pb_codec:decode_map_nested_update'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_map_key'(map_key()) -> antidote_pb:'ApbMapKey'().
'antidote_pb_codec:encode_map_key'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_map_key'(antidote_pb:'ApbMapKey'()) -> dec_map_key().
'antidote_pb_codec:decode_map_key'(_) -> error(overlay).

%% --- map responses ---

-spec 'antidote_pb_codec:encode_map_get_resp'([map_entry()]) -> antidote_pb:'ApbGetMapResp'().
'antidote_pb_codec:encode_map_get_resp'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_map_get_resp'(antidote_pb:'ApbGetMapResp'()) -> [map_entry()].
'antidote_pb_codec:decode_map_get_resp'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_map_entry'(map_entry()) -> antidote_pb:'ApbMapEntry'().
'antidote_pb_codec:encode_map_entry'(_) -> error(overlay).

-spec 'antidote_pb_codec:decode_map_entry'(antidote_pb:'ApbMapEntry'()) -> map_entry().
'antidote_pb_codec:decode_map_entry'(_) -> error(overlay).

%% --- cluster management ---

-spec 'antidote_pb_codec:encode_node'(node() | iodata()) -> binary().
'antidote_pb_codec:encode_node'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_create_dc'([node()]) -> antidote_pb:'ApbCreateDC'().
'antidote_pb_codec:encode_create_dc'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_create_dc_response'(ok | {error, antidote_pb_codec:error_code()}) -> antidote_pb:'ApbCreateDCResp'().
'antidote_pb_codec:encode_create_dc_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_get_connection_descriptor'() -> antidote_pb:'ApbGetConnectionDescriptor'().
'antidote_pb_codec:encode_get_connection_descriptor'() -> error(overlay).

-spec 'antidote_pb_codec:encode_get_connection_descriptor_response'({ok, Descriptor :: binary()} | {error, antidote_pb_codec:error_code()}) ->
          antidote_pb:'ApbGetConnectionDescriptorResp'().
'antidote_pb_codec:encode_get_connection_descriptor_response'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_connect_to_dcs'(Descriptors :: [binary()]) -> antidote_pb:'ApbConnectToDCs'().
'antidote_pb_codec:encode_connect_to_dcs'(_) -> error(overlay).

-spec 'antidote_pb_codec:encode_connect_to_dcs_response'(ok | {error, antidote_pb_codec:error_code()}) -> antidote_pb:'ApbConnectToDCsResp'().
'antidote_pb_codec:encode_connect_to_dcs_response'(_) -> error(overlay).
