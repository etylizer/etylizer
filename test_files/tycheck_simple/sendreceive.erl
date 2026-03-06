-module(sendreceive).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% SEND %%%%%%%%%%%%%%%%%%%%%%%

-spec send_01(pid(), integer()) -> integer().
send_01(Pid, Msg) -> Pid ! Msg.

-spec send_02(pid(), atom()) -> atom().
send_02(Pid, Msg) -> Pid ! Msg.

-spec send_03_fail(pid(), integer()) -> atom().
send_03_fail(Pid, Msg) -> Pid ! Msg.

-spec send_04(atom(), {atom(), pid()}) -> {atom(), pid()}.
send_04(RegName, Msg) -> RegName ! Msg.

-spec send_05(pid()) -> ok.
send_05(Pid) -> Pid ! ok.

-spec send_06_fail(string()) -> ok.
send_06_fail(Pid) -> Pid ! ok.

%%%%%%%%%%%%%%%%%%%%%%%% RECEIVE %%%%%%%%%%%%%%%%%%%%%%%

-spec recv_01() -> ok.
recv_01() ->
    receive
        ok -> ok
    end.

-spec recv_02() -> integer().
recv_02() ->
    receive
        X when is_integer(X) -> X
    end.

-spec recv_03() -> atom().
recv_03() ->
    receive
        hello -> hello;
        world -> world
    end.

-spec recv_04() -> {atom(), integer()}.
recv_04() ->
    receive
        {Tag, Val} -> {Tag, Val}
    end.

-spec recv_05_fail() -> {atom(), integer()}.
recv_05_fail() ->
    receive
        Tag when is_integer(Tag) -> Tag
    end.

% shadowing
-spec recv_06_fail(any()) -> {atom(), integer()}.
recv_06_fail(Tag) ->
    receive
        Tag when is_integer(Tag) -> Tag
    end.

%%%%%%%%%%%%%%%%%%%%%%%% RECEIVE WITH AFTER %%%%%%%%%%%%%%%%%%%%%%%

-spec recv_after_01() -> ok | timeout.
recv_after_01() ->
    receive ok -> ok after 1000 -> timeout end.

-spec recv_after_02() -> integer().
recv_after_02() ->
    receive
        X when is_integer(X) -> X
    after
        5000 -> 0
    end.

-spec recv_after_03() -> ok.
recv_after_03() ->
    receive after 100 -> ok end.

-spec recv_after_04_fail() -> integer().
recv_after_04_fail() ->
    receive ok -> ok after 1000 -> timeout end.

-spec recv_after_05() -> any().
recv_after_05() ->
    receive ok -> ok after infinity -> timeout end.

-spec recv_after_06_fail() -> any().
recv_after_06_fail() ->
    receive ok -> ok after bad -> timeout end.

%%%%%%%%%%%%%%%%%%%%%%%% RECEIVE LOOPS %%%%%%%%%%%%%%%%%%%%%%%

% Receive loop that returns ok
-spec recv_loop_01() -> ok.
recv_loop_01() ->
  receive
    quit ->
      ok;
    _Foo ->
      recv_loop_01()
  end.

% Receive loop with wrong return type
-spec recv_loop_02_fail() -> nok.
recv_loop_02_fail() ->
  receive
    quit ->
      ok;
    _Foo ->
      recv_loop_02_fail()
  end.

% Receive loop result bound to variable
-spec recv_loop_03() -> ok.
recv_loop_03() ->
  A = receive
    quit ->
      ok;
    _Foo ->
      recv_loop_03()
  end,
  A.

% Receive loop with timeout
-spec recv_loop_after_01() -> ok.
recv_loop_after_01() ->
  receive
    quit ->
      ok;
    _Foo ->
      recv_loop_after_01()
  after 1000 -> ok
  end.

% Receive loop with timeout, wrong return
-spec recv_loop_after_02_fail() -> nok.
recv_loop_after_02_fail() ->
  receive
    quit ->
      nok;
    _Foo ->
      recv_loop_after_02_fail()
  after 1000 -> ok
  end.

% Receive loop with timeout, bound result
-spec recv_loop_after_03() -> ok.
recv_loop_after_03() ->
  A = receive
    quit ->
      ok;
    _Foo ->
      recv_loop_after_03()
    after 1000 -> ok
  end,
  A.

%%%%%%%%%%%%%%%%%%%%%%%% COMBINED %%%%%%%%%%%%%%%%%%%%%%%

-spec send_recv_01(pid()) -> ok.
send_recv_01(Pid) ->
    Pid ! hello,
    receive
        ok -> ok
    end.
