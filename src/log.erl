-module(log).

% @doc Logging module. The logging module that comes with Erlang with too difficult
% to setup.

-export([num_level/1, init/1, allow/1, macro_log/5, parse_level/1, shutdown/0]).
-export_type([log_level/0]).

-type log_level() :: trace | debug | info | note | warn | error | abort.

-spec num_level(log_level()) -> integer().
num_level(L) ->
    case L of
        abort -> 0;
        error -> 1;
        warn -> 2;
        note -> 3;
        info -> 4;
        debug -> 5;
        trace -> 6
    end.

-spec init(log_level() | default) -> ok.
init(L1) ->
    L = get_log_level(L1),
    ets:new(log_config, [named_table, protected, set]),
    ets:insert(log_config, {level, L}),
    Pid = spawn_link(fun file_logger/0),
    ets:insert(log_config, {logger_pid, Pid}),
    io:format("Initialized logging with level ~s~n", [format_level(L1)]),
    ok.

-spec get_log_level(log_level() | default) -> log_level().
get_log_level(L) ->
    case L of
        default ->
            case os:getenv("ETY_LOG_LEVEL") of
                false -> warn;
                S ->
                    case parse_level(S) of
                        bad_log_level ->
                            io:format(standard_error,
                                      "Bad log level in environment variable ETY_LOG_LEVEL: ~p", S),
                            warn;
                        X -> X
                    end
            end;
        X -> X
    end.

-spec lazy_init() -> log_level().
lazy_init() ->
    Level = get_log_level(default),
    init(Level),
    Level.

-spec get_logger_pid() -> pid() | none.
get_logger_pid() ->
    Table = ets:whereis(log_config),
    case ets:lookup(Table, logger_pid) of
        [] -> none;
        [{_, Pid}] -> Pid
    end.

-spec shutdown() -> ok.
shutdown() ->
    case get_logger_pid() of
        none -> ok;
        Pid ->
            Pid ! {shutdown, self()},
            receive
                shutdown_done -> ok
            end
    end.

-spec file_logger() -> ok.
file_logger() ->
    {ok, F} = file:open("ety.log", [write]),
    Loop =
        fun Loop() ->
                receive
                    {log, Msg, Sender} ->
                        io:put_chars(F, Msg),
                        Sender ! log_ok,
                        %file:datasync(F),
                        Loop();
                    {shutdown, Pid} ->
                        Pid ! shutdown_done,
                        ok
                end
        end,
    Loop().

-spec allow(log_level()) -> boolean().
allow(L) ->
    Table = ets:whereis(log_config),
    MaxL =
        case Table of
            undefined -> lazy_init();
            T ->
                [{_, X}] = ets:lookup(T, level),
                X
        end,
    num_level(L) =< num_level(MaxL).

-spec format_level(log_level() | default) -> string().
format_level(L) ->
    case L of
        abort -> "ABORT";
        error -> "ERROR";
        warn -> "WARN";
        note -> "NOTE";
        info -> "INFO";
        debug -> "DEBUG";
        trace -> "TRACE";
        default -> "default"
    end.

-spec parse_level(string()) -> log_level() | bad_log_level.
parse_level(S) ->
    case string:lowercase(S) of
        "abort" -> abort;
        "error" -> error;
        "warn" -> warn;
        "note" -> note;
        "info" -> info;
        "debug" -> debug;
        "trace" -> trace;
        _ -> bad_log_level
    end.

-spec log_to_file(string()) -> ok.
log_to_file(S) ->
    case get_logger_pid() of
        none -> ok;
        Pid ->
            Pid ! {log, S, self()},
            receive
                log_ok -> ok
            end
    end.

-spec macro_log(string(), integer(), log_level(), string(), [any()]) -> ok.
macro_log(File, Line, Level, Msg, Args) ->
    {{Y,M,D},{H,MM,SS}} = calendar:now_to_datetime(erlang:timestamp()),
    S = utils:sformat("[~s ~B-~2.10.0B-~2.10.0B ~2.10.0B:~2.10.0B:~2.10.0B ~s:~b] " ++ Msg ++ "~n",
                      [format_level(Level), Y, M, D, H, MM, SS, filename:basename(File), Line | Args]),
    log_to_file(S),
    case num_level(Level) >= num_level(debug) of
        false -> io:put_chars(S);
        true -> ok
    end,
    ok.
