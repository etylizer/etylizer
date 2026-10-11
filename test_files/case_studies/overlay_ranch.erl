%% Specs for the functions of the ranch case study that have none in the source.
-module(overlay_ranch).
-compile([export_all, nowarn_export_all]).

%% an element of the socket options that ranch:filter_options/4 takes
-type user_option() :: inet | inet6 | {atom(), any()} | {raw, any(), any(), any()}.
%% the options of a handshake: none, or those given to ranch:handshake/2 and ranch:handshake_continue/2
-type handshake_opts() :: undefined | {opts, any()}.
%% what the handshake of a transport gives, see the callbacks of ranch_transport
-type handshake() :: {ok, ranch_transport:socket()} | {ok, ranch_transport:socket(), Info :: any()} | {error, any()}.
-type handshake_continue() :: {ok, ranch_transport:socket()} | {error, any()}.
%% what ranch:listener_info/2 builds, the value of ranch:info/1
-type listener_info() :: #{
    pid => pid(),
    status => running | suspended,
    ip => inet:ip_address() | {local, binary()} | undefined,
    port => inet:port_number() | undefined,
    max_connections => ranch:max_conns(),
    active_connections => non_neg_integer(),
    all_connections => non_neg_integer(),
    transport => module(),
    transport_options => ranch:transport_opts(any()),
    protocol => module(),
    protocol_options => any()
}.
%% #state{} of ranch_conns_sup
-type conns_sup_state() :: {state, Parent :: pid(), ranch:ref(), ranch_conns_sup:conn_type(), ranch_conns_sup:shutdown(),
                            Transport :: module(), Protocol :: module(), ProtoOpts :: any(), HandshakeTimeout :: timeout(),
                            ranch:max_conns(), Logger :: module()}.
%% #state{} of ranch_server
-type server_state() :: {state, ranch_server:monitors()}.
%% the value of the key ssl of a ranch_proxy_header:proxy_info()
-type proxy_ssl() :: #{
    client := [ssl | cert_conn | cert_sess],
    verified := boolean(),
    version => binary(),
    cipher => binary(),
    sig_alg => binary(),
    key_alg => binary(),
    cn => binary()
}.
-type proxy_family() :: undefined | ipv4 | ipv6 | unix.
-type proxy_protocol() :: undefined | stream | dgram.
%% what ranch_proxy_header:parse/1 gives
-type parsed() :: {ok, ranch_proxy_header:proxy_info(), Rest :: binary()} | {error, atom()}.

%% --- ranch ---

-spec 'ranch:maybe_started'(supervisor:startchild_ret()) -> supervisor:startchild_ret().
'ranch:maybe_started'(_) -> error(overlay).

-spec 'ranch:start_error'(Reason :: term(), Error) -> {error, eaddrinuse | eacces | no_cert} | Error.
'ranch:start_error'(_, _) -> error(overlay).

%% takes the result of supervisor:restart_child/2
-spec 'ranch:maybe_resumed'({ok, supervisor:child()} | {ok, supervisor:child(), Info :: term()} | {error, term()}) ->
          ok | {error, term()}.
'ranch:maybe_resumed'(_) -> error(overlay).

%% {error, Atom} when the supervisor of the acceptors is not running
-spec 'ranch:do_acceptors'(ListenerSup :: pid(), terminate_child | restart_child) -> ok | {error, undefined | restarting}.
'ranch:do_acceptors'(_, _) -> error(overlay).

-spec 'ranch:handshake1'(ranch:ref(), handshake_opts()) -> {ok, ranch_transport:socket()} | {continue, any()}.
'ranch:handshake1'(_, _) -> error(overlay).

-spec 'ranch:handshake_continue1'(ranch:ref(), handshake_opts()) -> {ok, ranch_transport:socket()}.
'ranch:handshake_continue1'(_, _) -> error(overlay).

%% handshake_continue of a transport does not give {ok, Socket, Info}
-spec 'ranch:handshake_transport'
        (Transport :: module(), handshake, ranch_transport:socket(), handshake_opts(), timeout()) -> handshake();
        (Transport :: module(), handshake_continue, ranch_transport:socket(), handshake_opts(), timeout()) -> handshake_continue().
'ranch:handshake_transport'(_, _, _, _, _) -> error(overlay).

%% {continue, Info} only for a handshake that gave {ok, Socket, Info}: ranch:handshake_continue/1,2 give {ok, Socket}
-spec 'ranch:handshake_result'({ok, Socket} | {ok, Socket, Info} | {error, any()}, ranch:ref(), Transport :: module(),
                               ranch_transport:socket(), timeout()) -> {ok, Socket} | {continue, Info}.
'ranch:handshake_result'(_, _, _, _, _) -> error(overlay).

-spec 'ranch:apply_transport_options'(ranch:ref(), ranch:transport_opts(any())) -> ok.
'ranch:apply_transport_options'(_, _) -> error(overlay).

-spec 'ranch:listener_info'(ranch:ref(), ListenerSup :: pid()) -> listener_info().
'ranch:listener_info'(_, _) -> error(overlay).

%% a child that is not running is undefined or restarting: the acceptors after ranch:stop_all_acceptors/0
-spec 'ranch:procs1'(ListenerSup :: pid(), acceptors | connections) -> [pid() | undefined | restarting].
'ranch:procs1'(_, _) -> error(overlay).

%% The three validate functions check what ranch:wait_for_connections/4 is given: any term, an error if it is not valid.
-spec 'ranch:validate_op'(Op :: term(), NumConns :: term()) -> ok.
'ranch:validate_op'(_, _) -> error(overlay).

-spec 'ranch:validate_num_conns'(NumConns :: term()) -> ok.
'ranch:validate_num_conns'(_) -> error(overlay).

-spec 'ranch:validate_interval'(Interval :: term()) -> ok.
'ranch:validate_interval'(_) -> error(overlay).

-spec 'ranch:wait_for_connections_loop'(ranch:ref(), '>' | '>=' | '==' | '=<' | '<', non_neg_integer(), non_neg_integer()) -> ok.
'ranch:wait_for_connections_loop'(_, _, _, _) -> error(overlay).

-spec 'ranch:filter_user_options'([user_option()], DisallowedKeys :: [atom()], Logger :: module()) -> [user_option()].
'ranch:filter_user_options'(_, _, _) -> error(overlay).

%% the option is one that filter_user_options/3 does not let through
-spec 'ranch:filter_options_warning'(Opt :: term(), Logger :: module()) -> ok.
'ranch:filter_options_warning'(_, _) -> error(overlay).

-spec 'ranch:merge_options'(user_option(), Acc :: [any()]) -> [any()].
'ranch:merge_options'(_, _) -> error(overlay).

%% --- ranch_acceptor ---

-spec 'ranch_acceptor:flush'(Logger :: module()) -> ok.
'ranch_acceptor:flush'(_) -> error(overlay).

%% --- ranch_acceptors_sup ---

-spec 'ranch_acceptors_sup:format_error'(Reason :: atom()) -> string().
'ranch_acceptors_sup:format_error'(_) -> error(overlay).

%% --- ranch_app ---

%% the result of eprof:start_profiling/1, or not_profiling
-spec 'ranch_app:consider_profiling'() -> profiling | {error, term()} | not_profiling.
'ranch_app:consider_profiling'() -> error(overlay).

%% --- ranch_conns_sup ---

-spec 'ranch_conns_sup:loop'(conns_sup_state(), CurConns :: non_neg_integer(), NbChildren :: non_neg_integer(),
                             Sleepers :: [pid()]) -> no_return().
'ranch_conns_sup:loop'(_, _, _, _) -> error(overlay).

-spec 'ranch_conns_sup:handshake'(conns_sup_state(), CurConns :: non_neg_integer(), NbChildren :: non_neg_integer(),
                                  Sleepers :: [pid()], To :: pid(), ranch_transport:socket(), SupPid :: pid(),
                                  ProtocolPid :: pid()) -> no_return().
'ranch_conns_sup:handshake'(_, _, _, _, _, _, _, _) -> error(overlay).

-spec 'ranch_conns_sup:set_transport_options'(conns_sup_state(), CurConns :: non_neg_integer(), NbChildren :: non_neg_integer(),
                                              Sleepers :: [pid()], ranch:transport_opts(any())) -> no_return().
'ranch_conns_sup:set_transport_options'(_, _, _, _, _) -> error(overlay).

-spec 'ranch_conns_sup:kill_children'([pid()]) -> ok.
'ranch_conns_sup:kill_children'(_) -> error(overlay).

-spec 'ranch_conns_sup:shutdown_children'([pid()]) -> ok.
'ranch_conns_sup:shutdown_children'(_) -> error(overlay).

-spec 'ranch_conns_sup:wait_children'(NbChildren :: non_neg_integer()) -> ok.
'ranch_conns_sup:wait_children'(_) -> error(overlay).

-spec 'ranch_conns_sup:report_error'(Logger :: module(), ranch:ref(), Protocol :: module(), pid(), Reason :: term()) -> ok.
'ranch_conns_sup:report_error'(_, _, _, _, _) -> error(overlay).

%% --- ranch_crc32c ---

-spec 'ranch_crc32c:do_crc32c'(non_neg_integer(), binary()) -> non_neg_integer().
'ranch_crc32c:do_crc32c'(_, _) -> error(overlay).

%% --- ranch_proxy_header ---

-spec 'ranch_proxy_header:parse_v1'(binary()) -> parsed().
'ranch_proxy_header:parse_v1'(_) -> error(overlay).

-spec 'ranch_proxy_header:parse_v1'(binary(), ipv4 | ipv6) -> parsed().
'ranch_proxy_header:parse_v1'(_, _) -> error(overlay).

-spec 'ranch_proxy_header:parse_ip'(binary(), ipv4 | ipv6) -> {ok, inet:ip_address(), Rest :: binary()}.
'ranch_proxy_header:parse_ip'(_, _) -> error(overlay).

-spec 'ranch_proxy_header:parse_ipv4'(Addr :: binary(), Rest :: binary()) -> {ok, inet:ip4_address(), Rest :: binary()}.
'ranch_proxy_header:parse_ipv4'(_, _) -> error(overlay).

-spec 'ranch_proxy_header:parse_ipv6'(Addr :: binary(), Rest :: binary()) -> {ok, inet:ip6_address(), Rest :: binary()}.
'ranch_proxy_header:parse_ipv6'(_, _) -> error(overlay).

%% One name for two functions: (Data, Separator) cuts off the digits before the separator, (Digits, Rest)
%% converts them. A Data that ends before the separator falls through to the second and comes back with the
%% separator as the rest: parse_v1/2 then fails on it, inside its try.
-spec 'ranch_proxy_header:parse_port'(binary(), Separator :: char() | binary()) ->
          {ok, inet:port_number(), Rest :: char() | binary()}.
'ranch_proxy_header:parse_port'(_, _) -> error(overlay).

-spec 'ranch_proxy_header:parse_v2'(binary()) -> parsed().
'ranch_proxy_header:parse_v2'(_) -> error(overlay).

-spec 'ranch_proxy_header:parse_family'(0..3) -> proxy_family().
'ranch_proxy_header:parse_family'(_) -> error(overlay).

-spec 'ranch_proxy_header:parse_protocol'(0..2) -> proxy_protocol().
'ranch_proxy_header:parse_protocol'(_) -> error(overlay).

%% Header is what the checksum is computed over
-spec 'ranch_proxy_header:parse_v2'(binary(), Len :: non_neg_integer(), proxy_family(), proxy_protocol(), Header :: binary()) ->
          parsed().
'ranch_proxy_header:parse_v2'(_, _, _, _, _) -> error(overlay).

%% Len is negative when a TLV is longer than what is left
-spec 'ranch_proxy_header:parse_tlv'(binary(), Len :: integer(), ranch_proxy_header:proxy_info(), Header :: binary()) -> parsed().
'ranch_proxy_header:parse_tlv'(_, _, _, _) -> error(overlay).

-spec 'ranch_proxy_header:parse_client'(<<_:8>>) -> [ssl | cert_conn | cert_sess].
'ranch_proxy_header:parse_client'(_) -> error(overlay).

-spec 'ranch_proxy_header:parse_ssl_tlv'(binary(), Len :: integer(), proxy_ssl()) -> {ok, proxy_ssl(), Rest :: binary()} | {error, atom()}.
'ranch_proxy_header:parse_ssl_tlv'(_, _, _) -> error(overlay).

-spec 'ranch_proxy_header:ssl_subtype'(byte()) -> version | cn | cipher | sig_alg | key_alg | undefined.
'ranch_proxy_header:ssl_subtype'(_) -> error(overlay).

-spec 'ranch_proxy_header:family'(ipv4 | ipv6 | unix) -> 1..3.
'ranch_proxy_header:family'(_) -> error(overlay).

-spec 'ranch_proxy_header:protocol'(stream | dgram) -> 1 | 2.
'ranch_proxy_header:protocol'(_) -> error(overlay).

-spec 'ranch_proxy_header:addresses'(ranch_proxy_header:proxy_info()) -> binary().
'ranch_proxy_header:addresses'(_) -> error(overlay).

-spec 'ranch_proxy_header:tlvs'(ranch_proxy_header:proxy_info(), ranch_proxy_header:build_opts()) -> iodata().
'ranch_proxy_header:tlvs'(_, _) -> error(overlay).

%% the TLV for the binary at Key, nothing if the map does not have it
-spec 'ranch_proxy_header:binary_tlv'(ranch_proxy_header:proxy_info() | proxy_ssl(), Key :: atom(), Type :: byte()) -> binary().
'ranch_proxy_header:binary_tlv'(_, _, _) -> error(overlay).

-spec 'ranch_proxy_header:noop_tlv'(ranch_proxy_header:build_opts()) -> binary().
'ranch_proxy_header:noop_tlv'(_) -> error(overlay).

-spec 'ranch_proxy_header:ssl_tlv'(ranch_proxy_header:proxy_info()) -> iodata().
'ranch_proxy_header:ssl_tlv'(_) -> error(overlay).

-spec 'ranch_proxy_header:client'([ssl | cert_conn | cert_sess], Acc :: non_neg_integer()) -> non_neg_integer().
'ranch_proxy_header:client'(_, _) -> error(overlay).

-spec 'ranch_proxy_header:raw_tlvs'(ranch_proxy_header:proxy_info()) -> [binary()].
'ranch_proxy_header:raw_tlvs'(_) -> error(overlay).

%% --- ranch_server ---

-spec 'ranch_server:set_monitored_process'({conns_sup, ranch:ref(), Id :: pos_integer()} | {listener_sup, ranch:ref()}, pid(),
                                           server_state()) -> server_state().
'ranch_server:set_monitored_process'(_, _, _) -> error(overlay).

%% --- ranch_server_proxy ---

-spec 'ranch_server_proxy:wait_ranch_server'(Tries :: non_neg_integer()) -> {ok, reference()} | {error, noproc}.
'ranch_server_proxy:wait_ranch_server'(_) -> error(overlay).
