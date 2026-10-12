%% Library specs of gen and sys for gen_fsm_compat, the one module of the riak_core_lite case study that
%% calls them. They name types of gen and sys, so they are kept out of the overlay for all modules.
-module(overlay_riak_core_lite_lib_gen).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% OTP: gen:start_ret(), which has {ok, {pid(), reference()}} for the linkage monitor. With link and
%% nolink the result is the one of proc_lib:start_link/5 and proc_lib:start/5.
-spec 'gen:start'(module(), link | nolink, module(), term(), [gen:option()]) -> {ok, pid()} | ignore | {error, term()}.
'gen:start'(_, _, _, _, _) -> error(overlay).

-spec 'gen:start'(module(), link | nolink, gen:emgr_name(), module(), term(), [gen:option()]) ->
          {ok, pid()} | ignore | {error, term()}.
'gen:start'(_, _, _, _, _, _) -> error(overlay).

%% OTP: a sys:format_fun(), which takes every sys:system_event(), any Extra and io:device() |
%% file:io_device(). handle_debug/4 calls the fun with the event and the Extra of this call, or keeps
%% the three together for sys:print_log/1; the device is standard_io or the log file, which sys opens
%% without raw, so it is an io:device().
-spec 'sys:handle_debug'([sys:dbg_opt()], fun((io:device(), Event, Extra) -> any()), Extra, Event) -> [sys:dbg_opt()].
'sys:handle_debug'(_, _, _, _) -> error(overlay).
