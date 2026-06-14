-module(web_driver_ex).

%% Persistent, non-halting driver for the browser/WASM etylizer **Elixir** mode.
%%
%% etylizer type checks Elixir by reading the Erlang abstract forms stored in a
%% compiled module's debug_info (see parse_beam). So for a live editor we must
%% compile the edited `.ex` source to a BEAM in-process (no mix/elixirc
%% subprocess), then run etylizer on the result. The protocol matches web_driver
%% (the Erlang driver): poll /work/gen, emit @@ETY_BEGIN/@@ETY_END frames.
%%
%%   * /work/input.ex  - the current editor buffer (JS writes it)
%%   * /work/gen       - bumped to request a re-check
%%   * /work/_etybeam/ - scratch dir for the compiled Elixir.*.beam

-export([start/0, check/1, init_elixir/0, compile_to_beams/1]).

-include("etylizer_main.hrl").
-include("etylizer.hrl").

-define(INPUT, "/work/input.ex").
-define(GEN, "/work/gen").
-define(POLL_MS, 80).
%% Elixir's own ebin, staged at the same path in the wasm MEMFS image as natively
%% so etylizer can load elixir_erl (the debug_info backend) + resolve stdlib specs.
-define(ELIXIR_EBIN, "/usr/lib/elixir/lib/elixir/ebin").

-spec start() -> no_return().
start() ->
    %% On wasm the baked image ships an older etylizer_main; force the patched one.
    catch code:load_abs("/over/ebin/etylizer_main"),
    init_elixir(),
    log:init(default, "/work/etylizer.log"),
    io:format("@@ETY_READY~n", []),
    loop(undefined).

-spec init_elixir() -> ok.
init_elixir() ->
    %% Put Elixir's apps on the code path (plain `erl` doesn't; the `elixir`
    %% wrapper does). Same location natively and in the staged wasm image.
    _ = [ code:add_patha(D) || D <- filelib:wildcard("/usr/lib/elixir/lib/*/ebin") ],
    {ok, _} = ?assert_pattern({ok, _}, application:ensure_all_started(elixir)),
    %% Re-compiling the same module on every edit would otherwise warn/err.
    % Elixir is not on the search path of the checker: its functions are called by name
    _ = erlang:apply('Elixir.Code', compiler_options, [#{ignore_module_conflict => true}]),
    ok.

-spec loop(term()) -> no_return().
loop(LastGen) ->
    case read_gen() of
        LastGen -> timer:sleep(?POLL_MS), loop(LastGen);
        Gen -> emit(Gen, check(?INPUT)), loop(Gen)
    end.

-spec read_gen() -> string().
read_gen() ->
    case file:read_file(?GEN) of
        {ok, Bin} -> string:trim(binary_to_list(Bin));
        _ -> ""
    end.

%% Compile the .ex buffer in-process, then run etylizer on the produced beams.
%% Returns ok | {error, Kind, Message}; never raises.
-spec check(file:filename()) -> ok | {error, atom(), string()}.
check(ExFile) ->
    _ = init_elixir(),
    try
        {ok, SrcBin} = ?assert_pattern({ok, _}, file:read_file(ExFile)),
        case compile_ex(SrcBin, ExFile) of
            {ok, Beams} ->
                BeamPaths = write_beams(ExFile, Beams),
                run_etylizer(BeamPaths);
            {compile_error, Msg} ->
                {error, compile_error, Msg}
        end
    catch
        throw:{etylizer, EKind0, EMsg0} ->
            {EKind, EMsg} = errors:caught(EKind0, EMsg0),
            {error, EKind, EMsg};
        Class:Reason:Stack ->
            {error, internal,
             lists:flatten(io_lib:format("~p:~p~n~p", [Class, Reason, Stack]))}
    end.

%% Compile the .ex buffer in-process and write the modules to a scratch ebin.
%% Returns the beam paths (to feed etylizer) or a compile-error diagnostic.
-spec compile_to_beams(file:filename()) ->
    {ok, [file:filename()]} | {compile_error, string()}.
compile_to_beams(ExFile) ->
    _ = init_elixir(),
    {ok, SrcBin} = ?assert_pattern({ok, _}, file:read_file(ExFile)),
    case compile_ex(SrcBin, ExFile) of
        {ok, Beams} -> {ok, write_beams(ExFile, Beams)};
        {compile_error, Msg} -> {compile_error, Msg}
    end.

%% In-process Elixir compile. Returns {ok, [{Module, BeamBinary}]} or a
%% {compile_error, Message} with the source location when the source is invalid.
-spec compile_ex(binary(), file:filename()) ->
    {ok, [{module(), binary()}]} | {compile_error, string()}.
compile_ex(SrcBin, ExFile) ->
    FileBin = ?assert_pattern(<<_/binary>>, unicode:characters_to_binary(ExFile)),
    try erlang:apply('Elixir.Code', compile_string, [SrcBin, FileBin]) of
        % what the Elixir compiler returns: the modules with their object code
        Beams when is_list(Beams) -> {ok, ?assert_type(Beams, [{module(), binary()}])};
        NoList -> {compile_error, format_ex_error(ExFile, NoList)}
    catch
        error:Ex:_ -> {compile_error, format_ex_error(ExFile, Ex)};
        _:Other:_  -> {compile_error, format_ex_error(ExFile, Other)}
    end.

%% Format an Elixir compile/syntax exception as "File:Line: Compile error: Msg".
-spec format_ex_error(file:filename(), term()) -> string().
format_ex_error(ExFile, Ex) when is_map(Ex) ->
    Line = case maps:get(line, Ex, undefined) of
               L when is_integer(L) -> L;
               _ -> 1
           end,
    Col = case maps:get(column, Ex, undefined) of
              C when is_integer(C) -> C;
              _ -> 1
          end,
    Msg = try erlang:apply('Elixir.Exception', message, [Ex])
          catch _:_ -> io_lib:format("~p", [Ex]) end,
    lists:flatten(io_lib:format("~s:~p:~p: Compile error: ~ts", [ExFile, Line, Col, Msg]));
format_ex_error(ExFile, Ex) ->
    lists:flatten(io_lib:format("~s: Compile error: ~p", [ExFile, Ex])).

%% Write each compiled module to a clean scratch ebin; return the beam paths.
-spec write_beams(file:filename(), [{module(), binary()}]) -> [file:filename()].
write_beams(ExFile, Beams) ->
    EbinDir = filename:join(filename:dirname(ExFile), "_etybeam"),
    ?assert_pattern(ok, filelib:ensure_dir(filename:join(EbinDir, "x"))),
    [ file:delete(F) || F <- filelib:wildcard(filename:join(EbinDir, "*.beam")) ],
    [ begin
          Path = filename:join(EbinDir, atom_to_list(Mod) ++ ".beam"),
          ?assert_pattern(ok, file:write_file(Path, Bin)),
          Path
      end || {Mod, Bin} <- Beams ].

-spec run_etylizer([file:filename()]) -> ok | {error, atom(), string()}.
run_etylizer(BeamPaths) ->
    Opts0 = etylizer_main:parse_args(["-a", ?ELIXIR_EBIN | BeamPaths]),
    Opts = Opts0#opts{log_file = "/work/etylizer.log"},
    try etylizer_main:doWork(Opts) of
        _ -> ok
    catch throw:{etylizer, Kind0, Msg0} ->
        {Kind, Msg} = errors:caught(Kind0, Msg0),
        {error, Kind, Msg}
    end.

-spec emit(string(), ok | {error, atom(), string()}) -> ok.
emit(Gen, ok) -> emit_block(Gen, "ok", "");
emit(Gen, {error, Kind, Msg}) -> emit_block(Gen, atom_to_list(Kind), Msg).

-spec emit_block(string(), string(), string()) -> ok.
emit_block(Gen, Status, Body) ->
    io:format("~n@@ETY_BEGIN ~s ~s~n~ts~n@@ETY_END~n", [Gen, Status, Body]).
