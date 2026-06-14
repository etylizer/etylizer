-module(web_driver).

%% Combined persistent driver for the browser editor's two tabs (Erlang + Elixir),
%% sharing one wasm BEAM. Both languages use etylizer's default **early-exit** mode:
%% the first type error is reported. (All-errors is deferred to etylizer's upcoming
%% report-mode JSON API.)
%%
%%   * /work/mode      - "erl" | "ex"   (JS writes it with the source)
%%   * /work/input.erl - Erlang buffer  (mode "erl")
%%   * /work/input.ex  - Elixir buffer  (mode "ex"; compiled in-process, see web_driver_ex)
%%   * /work/gen       - bumped to request a re-check
%%
%% Results stream back framed on stdout (JS parses the body into diagnostics):
%%   @@ETY_BEGIN <gen> report
%%   Error: <kind>
%%     <file:line:col: ... error: ...>            (nothing is printed on success)
%%   @@ETY_END

-export([start/0]).

-include("etylizer_main.hrl").

-define(GEN, "/work/gen").
-define(MODE, "/work/mode").
-define(POLL_MS, 80).
-define(ELIXIR_EBIN, "/usr/lib/elixir/lib/elixir/ebin").

-spec start() -> no_return().
start() ->
    log:init(default, "/work/etylizer.log"),
    io:format("@@ETY_READY~n", []),
    loop(undefined).

-spec loop(term()) -> no_return().
loop(LastGen) ->
    case read_file_trim(?GEN) of
        LastGen -> timer:sleep(?POLL_MS), loop(LastGen);
        Gen -> check(Gen, read_file_trim(?MODE)), loop(Gen)
    end.

%% Emit one framed check result for the given generation.
-spec check(string(), string()) -> ok.
check(Gen, Mode) ->
    io:format("~n@@ETY_BEGIN ~s report~n", [Gen]),
    case prepare(Mode) of
        {ok, Args} -> run(Args);
        {compile_error, Msg} -> error_entry("compile_error", Msg)
    end,
    io:format("@@ETY_END~n", []).

%% Build the etylizer argv for the active tab (compiling Elixir first).
-spec prepare(string()) -> {ok, [string()]} | {compile_error, string()}.
prepare("ex") ->
    case web_driver_ex:compile_to_beams("/work/input.ex") of
        {ok, BeamPaths} -> {ok, ["-a", ?ELIXIR_EBIN | BeamPaths]};
        {compile_error, Msg} -> {compile_error, Msg}
    end;
prepare(_) ->
    {ok, ["/work/input.erl"]}.

%% Run etylizer in early-exit mode (the parse_args default): doWork throws on the
%% first type error, which we print as one synthetic Error entry.
-spec run([string()]) -> ok.
run(Args) ->
    Opts0 = etylizer_main:parse_args(Args),
    Opts = Opts0#opts{log_file = "/work/etylizer.log"},
    try etylizer_main:doWork(Opts) of
        _ -> ok
    catch
        throw:{etylizer, Kind, Msg} -> error_entry(atom_to_list(Kind), to_text(Msg));
        Class:Reason:Stack ->
            error_entry("internal", lists:flatten(io_lib:format("~p:~p~n~p", [Class, Reason, Stack])))
    end.

-spec error_entry(string(), string()) -> ok.
error_entry(Kind, Msg) ->
    io:format(user, "Error: ~s~n  ~ts~n", [Kind, Msg]).

-spec read_file_trim(file:filename()) -> string().
read_file_trim(Path) ->
    case file:read_file(Path) of
        {ok, Bin} -> string:trim(binary_to_list(Bin));
        _ -> ""
    end.

-spec to_text(term()) -> string().
to_text(S) when is_list(S) -> S;
to_text(B) when is_binary(B) -> binary_to_list(B);
to_text(Other) -> lists:flatten(io_lib:format("~p", [Other])).
