%% Specs for the functions of the erlzmq case study that have none in the source: the NIFs.
%% They are what erlzmq.erl, the only caller, passes and expects.
-module(overlay_erlzmq).
-compile([export_all, nowarn_export_all]).

%% the types of the library
-include("erlzmq.hrl").

%% the handle inside an erlzmq_socket()
-type socket() :: binary().

-spec 'erlzmq_nif:init'() -> ok | {error, term()}.
'erlzmq_nif:init'() -> error(overlay).

-spec 'erlzmq_nif:context'(Threads :: pos_integer()) -> {ok, erlzmq_context()} | erlzmq_error().
'erlzmq_nif:context'(_) -> error(overlay).

-spec 'erlzmq_nif:socket'(erlzmq_context(), Type :: integer(), Active :: 0 | 1, ActivePid :: pid()) ->
          {ok, erlzmq_socket()} | erlzmq_error().
'erlzmq_nif:socket'(_, _, _, _) -> error(overlay).

-spec 'erlzmq_nif:bind'(socket(), Endpoint :: string()) -> ok | erlzmq_error().
'erlzmq_nif:bind'(_, _) -> error(overlay).

-spec 'erlzmq_nif:connect'(socket(), Endpoint :: string()) -> ok | erlzmq_error().
'erlzmq_nif:connect'(_, _) -> error(overlay).

%% a reference when the result comes later, as a message {Ref, Result}
-spec 'erlzmq_nif:send'(socket(), binary(), Flags :: integer()) -> ok | reference() | erlzmq_error().
'erlzmq_nif:send'(_, _, _) -> error(overlay).

-spec 'erlzmq_nif:recv'(socket(), Flags :: integer()) -> {ok, erlzmq_data()} | reference() | erlzmq_error().
'erlzmq_nif:recv'(_, _) -> error(overlay).

-spec 'erlzmq_nif:setsockopt'(socket(), OptionName :: integer(), OptionValue :: integer() | binary()) -> ok | erlzmq_error().
'erlzmq_nif:setsockopt'(_, _, _) -> error(overlay).

-spec 'erlzmq_nif:getsockopt'(socket(), OptionName :: integer()) -> {ok, erlzmq_sockopt_value()} | erlzmq_error().
'erlzmq_nif:getsockopt'(_, _) -> error(overlay).

-spec 'erlzmq_nif:close'(socket()) -> ok | reference() | erlzmq_error().
'erlzmq_nif:close'(_) -> error(overlay).

-spec 'erlzmq_nif:term'(erlzmq_context()) -> ok | reference() | erlzmq_error().
'erlzmq_nif:term'(_) -> error(overlay).

-spec 'erlzmq_nif:version'() -> {integer(), integer(), integer()}.
'erlzmq_nif:version'() -> error(overlay).
