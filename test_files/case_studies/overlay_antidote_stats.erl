%% Specs for the functions of the antidote_stats case study that have none in the source.
-module(overlay_antidote_stats).
-compile([export_all, nowarn_export_all]).

%% --- antidote_stats_app ---

-spec 'antidote_stats_app:start'(application:start_type(), StartArgs :: term()) -> {ok, pid()} | {error, term()}.
'antidote_stats_app:start'(_, _) -> error(overlay).

-spec 'antidote_stats_app:stop'(State :: term()) -> ok.
'antidote_stats_app:stop'(_) -> error(overlay).

%% --- antidote_stats_sup ---

-spec 'antidote_stats_sup:start_link'() -> {ok, pid()} | {error, term()}.
'antidote_stats_sup:start_link'() -> error(overlay).

-spec 'antidote_stats_sup:init'([]) -> {ok, {supervisor:sup_flags(), [supervisor:child_spec()]}}.
'antidote_stats_sup:init'(_) -> error(overlay).

%% --- antidote_stats_collector ---

-spec 'antidote_stats_collector:start_link'() -> {ok, pid()} | {error, term()}.
'antidote_stats_collector:start_link'() -> error(overlay).

-spec 'antidote_stats_collector:handle_call'(Req :: term(), gen_server:from(), antidote_stats_collector:state()) ->
          {reply, ok, antidote_stats_collector:state()}.
'antidote_stats_collector:handle_call'(_, _, _) -> error(overlay).

-spec 'antidote_stats_collector:handle_cast'(StatRequest :: term(), antidote_stats_collector:state()) ->
          {noreply, antidote_stats_collector:state()}.
'antidote_stats_collector:handle_cast'(_, _) -> error(overlay).

-spec 'antidote_stats_collector:terminate'(Reason :: term(), antidote_stats_collector:state()) -> ok.
'antidote_stats_collector:terminate'(_, _) -> error(overlay).

-spec 'antidote_stats_collector:code_change'(OldVsn :: term(), antidote_stats_collector:state(), Extra :: term()) ->
          {ok, antidote_stats_collector:state()}.
'antidote_stats_collector:code_change'(_, _, _) -> error(overlay).

-spec 'antidote_stats_collector:init_metrics'() -> ok.
'antidote_stats_collector:init_metrics'() -> error(overlay).
