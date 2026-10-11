%% Specs for the functions of the poolboy case study that have none in the source.
-module(overlay_poolboy).
-compile([export_all, nowarn_export_all]).

%% #state{} of poolboy, which has no type for it
-type state() :: {state, Supervisor :: undefined | pid(), Workers :: [pid()], Waiting :: poolboy:pid_queue(), Monitors :: ets:tid(),
                  Size :: non_neg_integer(), Overflow :: non_neg_integer(), MaxOverflow :: non_neg_integer(),
                  Strategy :: lifo | fifo}.

%% proplists:proplist(), spelled out: poolboy_sup does not load proplists, and naming a type of a module
%% that is not loaded crashes the engine
-type proplist() :: [atom() | tuple()].
%% the supervisor of the workers as #state{} has it: undefined until init/3 has seen worker_module
-type sup() :: undefined | pid().

%% --- poolboy ---

-spec 'poolboy:init'({PoolArgs :: proplist(), WorkerArgs :: proplist()}) -> {ok, state()}.
'poolboy:init'(_) -> error(overlay).

-spec 'poolboy:init'(PoolArgs :: proplist(), WorkerArgs :: proplist(), state()) -> {ok, state()}.
'poolboy:init'(_, _, _) -> error(overlay).

-spec 'poolboy:handle_cast'(Msg :: term(), state()) -> {noreply, state()}.
'poolboy:handle_cast'(_, _) -> error(overlay).

-spec 'poolboy:handle_call'(Msg :: term(), gen_server:from(), state()) ->
          {reply, term(), state()} | {noreply, state()} | {stop, normal, ok, state()}.
'poolboy:handle_call'(_, _, _) -> error(overlay).

-spec 'poolboy:handle_info'(Info :: term(), state()) -> {noreply, state()}.
'poolboy:handle_info'(_, _) -> error(overlay).

-spec 'poolboy:terminate'(Reason :: term(), state()) -> ok.
'poolboy:terminate'(_, _) -> error(overlay).

-spec 'poolboy:code_change'(OldVsn :: term(), state(), Extra :: term()) -> {ok, state()}.
'poolboy:code_change'(_, _, _) -> error(overlay).

-spec 'poolboy:start_pool'(start | start_link, PoolArgs :: proplist(), WorkerArgs :: proplist()) ->
          poolboy:start_ret().
'poolboy:start_pool'(_, _, _) -> error(overlay).

-spec 'poolboy:new_worker'(sup()) -> pid().
'poolboy:new_worker'(_) -> error(overlay).

-spec 'poolboy:new_worker'(sup(), FromPid :: pid()) -> {pid(), reference()}.
'poolboy:new_worker'(_, _) -> error(overlay).

-spec 'poolboy:dismiss_worker'(sup(), pid()) -> ok | {error, not_found | simple_one_for_one}.
'poolboy:dismiss_worker'(_, _) -> error(overlay).

-spec 'poolboy:prepopulate'(N :: integer(), sup()) -> [pid()].
'poolboy:prepopulate'(_, _) -> error(overlay).

-spec 'poolboy:prepopulate'(N :: non_neg_integer(), sup(), Workers :: [pid()]) -> [pid()].
'poolboy:prepopulate'(_, _, _) -> error(overlay).

-spec 'poolboy:handle_checkin'(pid(), state()) -> state().
'poolboy:handle_checkin'(_, _) -> error(overlay).

-spec 'poolboy:handle_worker_exit'(pid(), state()) -> state().
'poolboy:handle_worker_exit'(_, _) -> error(overlay).

-spec 'poolboy:state_name'(state()) -> full | overflow | ready.
'poolboy:state_name'(_) -> error(overlay).

%% --- poolboy_sup ---

-spec 'poolboy_sup:start_link'(Mod :: module(), Args :: proplist()) -> {ok, pid()} | ignore | {error, term()}.
'poolboy_sup:start_link'(_, _) -> error(overlay).

-spec 'poolboy_sup:init'({Mod :: module(), Args :: proplist()}) ->
          {ok, {{simple_one_for_one, 0, 1}, [supervisor:child_spec()]}}.
'poolboy_sup:init'(_) -> error(overlay).
