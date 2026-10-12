%% Specs for the functions of the antidotec_pb case study that have none in the source.
-module(overlay_antidotec_pb).
-compile([export_all, nowarn_export_all]).

%% #request{} of antidotec_pb_socket, which has no type for it
-type request() :: {request, Ref :: reference(), From :: term(), Timeout :: timeout(), Tref :: reference() | undefined}.
%% what antidotec_pb_socket:handle_call/3 answers
-type call() :: {req, Msg :: iodata(), timeout()} | {store_commit_time, TimeStamp :: term()} | get_commit_time | stop.
%% what antidotec_pb_socket:handle_info/2 expects
-type info() :: {tcp, port(), binary()} | {req_timeout, reference()} | {tcp_closed, port()}.

%% --- antidotec_counter ---

-spec 'antidotec_counter:to_ops'(BoundObject, antidotec_counter:antidotec_counter()) -> [{BoundObject, increment | decrement, integer()}].
'antidotec_counter:to_ops'(_, _) -> error(overlay).

%% --- antidotec_pb ---

-spec 'antidotec_pb:is_static'(TxnProperties :: term()) -> boolean().
'antidotec_pb:is_static'(_) -> error(overlay).

%% --- antidotec_pb_socket ---

-spec 'antidotec_pb_socket:start_link'(antidotec_pb_socket:address(), antidotec_pb_socket:portnum(), Options :: list()) ->
          {ok, pid()} | {error, term()}.
'antidotec_pb_socket:start_link'(_, _, _) -> error(overlay).

-spec 'antidotec_pb_socket:start'(antidotec_pb_socket:address(), antidotec_pb_socket:portnum()) -> {ok, pid()} | {error, term()}.
'antidotec_pb_socket:start'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:start'(antidotec_pb_socket:address(), antidotec_pb_socket:portnum(), Options :: list()) ->
          {ok, pid()} | {error, term()}.
'antidotec_pb_socket:start'(_, _, _) -> error(overlay).

-spec 'antidotec_pb_socket:stop'(pid()) -> ok.
'antidotec_pb_socket:stop'(_) -> error(overlay).

-spec 'antidotec_pb_socket:call_infinity'(pid(), Msg :: term()) -> term().
'antidotec_pb_socket:call_infinity'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:store_commit_time'(pid(), TimeStamp :: term()) -> ok.
'antidotec_pb_socket:store_commit_time'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:get_last_commit_time'(pid()) -> {ok, TimeStamp :: term()}.
'antidotec_pb_socket:get_last_commit_time'(_) -> error(overlay).

-spec 'antidotec_pb_socket:handle_call'(call(), gen_server:from(), antidotec_pb_socket:state()) ->
          {noreply, antidotec_pb_socket:state()} | {reply, ok | {ok, term()}, antidotec_pb_socket:state()}
        | {stop, normal, ok, antidotec_pb_socket:state()}.
'antidotec_pb_socket:handle_call'(_, _, _) -> error(overlay).

-spec 'antidotec_pb_socket:handle_info'(info(), antidotec_pb_socket:state()) ->
          {noreply, antidotec_pb_socket:state()} | {stop, disconnected, antidotec_pb_socket:state()}.
'antidotec_pb_socket:handle_info'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:handle_cast'(term(), antidotec_pb_socket:state()) -> {noreply, antidotec_pb_socket:state()}.
'antidotec_pb_socket:handle_cast'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:terminate'(Reason :: term(), antidotec_pb_socket:state()) -> ok.
'antidotec_pb_socket:terminate'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:code_change'(OldVsn :: term(), antidotec_pb_socket:state(), Extra :: term()) ->
          {ok, antidotec_pb_socket:state()}.
'antidotec_pb_socket:code_change'(_, _, _) -> error(overlay).

-spec 'antidotec_pb_socket:connect'(antidotec_pb_socket:state()) -> {ok, antidotec_pb_socket:state()} | {error, term()}.
'antidotec_pb_socket:connect'(_) -> error(overlay).

-spec 'antidotec_pb_socket:disconnect'(antidotec_pb_socket:state()) -> {stop, disconnected, antidotec_pb_socket:state()}.
'antidotec_pb_socket:disconnect'(_) -> error(overlay).

-spec 'antidotec_pb_socket:create_req_timer'(timeout() | undefined, reference()) -> reference() | undefined.
'antidotec_pb_socket:create_req_timer'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:maybe_reply'({noreply, antidotec_pb_socket:state()}) -> antidotec_pb_socket:state().
'antidotec_pb_socket:maybe_reply'(_) -> error(overlay).

-spec 'antidotec_pb_socket:send_caller'(Msg :: term(), request()) -> request().
'antidotec_pb_socket:send_caller'(_, _) -> error(overlay).

-spec 'antidotec_pb_socket:cancel_req_timer'(reference() | undefined) -> ok.
'antidotec_pb_socket:cancel_req_timer'(_) -> error(overlay).

%% --- antidotec_reg ---

-spec 'antidotec_reg:new'(Value :: term()) -> antidotec_reg:antidote_reg().
'antidotec_reg:new'(_) -> error(overlay).

-spec 'antidotec_reg:dirty_value'(antidotec_reg:antidote_reg()) -> term().
'antidotec_reg:dirty_value'(_) -> error(overlay).

-spec 'antidotec_reg:assign'(antidotec_reg:antidote_reg(), Value :: term()) -> antidotec_reg:antidote_reg().
'antidotec_reg:assign'(_, _) -> error(overlay).

%% --- antidotec_set ---

-spec 'antidotec_set:to_ops'(BoundObject, antidotec_set:antidote_set()) -> [{BoundObject, add_all | remove_all, [term()]}].
'antidotec_set:to_ops'(_, _) -> error(overlay).
