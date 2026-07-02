-module(sendreceive).

-compile(export_all).
-compile(nowarn_export_all).

% Define pid(_T) as a type alias for pid() so Erlang accepts pid(T) in specs.
% Etylizer gives pid(T) special semantics: T is the message type the process accepts.
-type pid(_T) :: pid().

% Declare per-function receive message types for typed receive checking.
% Format: -etylizer({msg_type, FunName, Arity, "TypeString"}).
% Must appear before function definitions (OTP 28+ requirement).
-etylizer({msg_type, recv_inter_01, 1, ["fun((1) -> ok)", "fun((any()) -> any())"]}).
-etylizer({msg_type, recv_open_01, 0, ["fun((integer()) -> atom())", "fun((term()) -> term())"]}).
-etylizer({msg_type, recv_open_02_fail, 0, ["fun((integer()) -> atom())", "fun((term()) -> term())"]}).
-etylizer({msg_type, recv_msg_01, 0, "integer()"}).
-etylizer({msg_type, recv_msg_02, 0, "integer()"}).
-etylizer({msg_type, recv_msg_03_fail, 0, "integer()"}).  % X gets integer(), but spec says atom()
-etylizer({msg_type, recv_msg_04, 0, "{ok, integer()}"}).
-etylizer({msg_type, recv_msg_05_fail, 0, "integer()"}).
-etylizer({msg_type, recv_msg_06_fail, 0, "atom()"}).
-etylizer({msg_type, recv_msg_07_fail, 0, "atom()"}).
-etylizer({msg_type, recv_msg_08_fail, 0, "atom()"}).
-etylizer({msg_type, recv_msg_09, 0, "integer() | atom()", noexhaustiveness}).
-etylizer({msg_type, recv_msg_10, 0, "{ok, integer()} | {error, atom()}", noexhaustiveness}).
-etylizer({msg_type, recv_msg_11_fail, 0, "atom()", noexhaustiveness}).
-etylizer({msg_type, ping_pong, 2, "integer()"}).
-etylizer({msg_type, stdlib_relay_01, 1, "integer()"}).
-etylizer({msg_type, stdlib_relay_02_fail, 1, "atom()"}).
-etylizer({msg_type, stdlib_sys_loop_01, 0, "{system, atom()} | {exit, atom()}"}).
-etylizer({msg_type, stdlib_sys_loop_02_fail, 0, "{system, atom()} | {exit, atom()}"}).
-etylizer({msg_type, stdlib_result_recv_01, 0, "{ok, integer()} | {error, atom()}"}).
-etylizer({msg_type, stdlib_result_recv_02_fail, 0, "{ok, integer()} | {error, atom()}"}).
-etylizer({msg_type, nested_relay_01, 1, "pid(integer())"}).
-etylizer({msg_type, nested_relay_02_fail, 1, "integer()"}).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.
%
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


%%%%%%%%%%%%%%%%%%%%%%%% TYPED PID (pid(T)) %%%%%%%%%%%%%%%%%%%%%%%

% Send an integer to a pid(integer())
-spec pid_send_01(pid(integer())) -> integer().
pid_send_01(Pid) -> Pid ! 42.

% Send an integer to a pid(atom())
-spec pid_send_02_fail(pid(atom())) -> integer().
pid_send_02_fail(Pid) -> Pid ! 42.

% Send a tuple to a pid({atom(), integer()})
-spec pid_send_04(pid({atom(), integer()})) -> {atom(), integer()}.
pid_send_04(Pid) -> Pid ! {ok, 1}.

%%%%%%%%%%%%%%%%%%%%%%%% TYPED RECEIVE (msg_type) %%%%%%%%%%%%%%%%%%%%%%%

% integer messages, result integer
%-etylizer({msg_type, recv_msg_01, 0, "integer()"}).
-spec recv_msg_01() -> integer().
recv_msg_01() ->
    receive
        X -> X
    end.

% redundant refinement guard
%-etylizer({msg_type, recv_msg_02, 0, "integer()"}).
-spec recv_msg_02() -> integer().
recv_msg_02() ->
    receive
        X when is_integer(X) -> X
    end.

% message is integer but expected atom() return
%-etylizer({msg_type, recv_msg_03_fail, 0, "integer()"}).
-spec recv_msg_03_fail() -> atom().
recv_msg_03_fail() ->
    receive
        X -> X
    end.

% extract integer from tuple type
%-etylizer({msg_type, recv_msg_04, 0, "{ok, integer()}"}).
-spec recv_msg_04() -> integer().
recv_msg_04() ->
    receive
        {ok, N} -> N
    end.

% ok branch is redundant
%-etylizer({msg_type, recv_msg_05_fail, 0, "integer()"}).
-spec recv_msg_05_fail() -> ok.
recv_msg_05_fail() ->
    receive ok -> ok; _ -> ok end.

% expects atom(), non-exhaustive
%-etylizer({msg_type, recv_msg_06_fail, 0, "atom()"}).
-spec recv_msg_06_fail() -> ok.
recv_msg_06_fail() ->
    receive ok -> ok end.

% two-branch non-exhaustive
%-etylizer({msg_type, recv_msg_07_fail, 0, "atom()"}).
-spec recv_msg_07_fail() -> ok | two.
recv_msg_07_fail() ->
    receive ok -> ok; two -> two end.

% redundant branch
%-etylizer({msg_type, recv_msg_08_fail, 0, "atom()"}).
-spec recv_msg_08_fail() -> ok.
recv_msg_08_fail() ->
    receive 42 -> ok; _ -> ok end.

% partial receive with noexhaustiveness 
% only handles integer(), atom() stays in mailbox.
%-etylizer({msg_type, recv_msg_09, 0, "integer() | atom()", noexhaustiveness}).
-spec recv_msg_09() -> integer().
recv_msg_09() ->
    receive X when is_integer(X) -> X end.

% Handle only {ok,...}
% {error,...} stays in mailbox
%-etylizer({msg_type, recv_msg_10, 0, "{ok, integer()} | {error, atom()}", noexhaustiveness}).
-spec recv_msg_10() -> integer().
recv_msg_10() ->
    receive {ok, N} -> N end.

% Redundancy with noexhaustiveness 
% 42 is not atom(), dead code
%-etylizer({msg_type, recv_msg_11_fail, 0, "atom()", noexhaustiveness}).
-spec recv_msg_11_fail() -> ok.
recv_msg_11_fail() ->
    receive 
        42 -> ok; 
        X when is_atom(X) -> ok 
    end.

% ping-pong protocol: typed send and receive
%-etylizer({msg_type, ping_pong, 2, "integer()"}).
-spec ping_pong(pid(integer()), integer()) -> integer().
ping_pong(Caller, N) ->
    Caller ! N,
    receive
        Reply -> Reply
    end.

%%%%%%%%%%%%%%%%%%%%%%%% STDLIB-INSPIRED PATTERNS %%%%%%%%%%%%%%%%%%%%%%%

% From slave:relay1

% Receive integer(), forward to pid(integer())
%-etylizer({msg_type, stdlib_relay_01, 1, "integer()"}).
-spec stdlib_relay_01(pid(integer())) -> no_return().
stdlib_relay_01(Pid) ->
    receive X -> Pid ! X end,
    stdlib_relay_01(Pid).

% msg_type is atom() but Pid expects an integer()
%-etylizer({msg_type, stdlib_relay_02_fail, 1, "atom()"}).
-spec stdlib_relay_02_fail(pid(integer())) -> no_return().
stdlib_relay_02_fail(Pid) ->
    receive X -> Pid ! X end,
    stdlib_relay_02_fail(Pid).

% From sys:suspend_loop, exhaustive & not redundant
%-etylizer({msg_type, stdlib_sys_loop_01, 0, "{system, atom()} | {exit, atom()}"}).
-spec stdlib_sys_loop_01() -> ok.
stdlib_sys_loop_01() ->
    receive
        {system, _} -> stdlib_sys_loop_01();
        {exit,   _} -> ok
    end.

% {exit,...} branch missing, not exhaustive
%-etylizer({msg_type, stdlib_sys_loop_02_fail, 0, "{system, atom()} | {exit, atom()}"}).
-spec stdlib_sys_loop_02_fail() -> ok.
stdlib_sys_loop_02_fail() ->
    receive
        {system, _} -> stdlib_sys_loop_02_fail()
    end.

% From gen.erl, receive result union
%-etylizer({msg_type, stdlib_result_recv_01, 0, "{ok, integer()} | {error, atom()}"}).
-spec stdlib_result_recv_01() -> ok.
stdlib_result_recv_01() ->
    receive
        {ok,    _} -> ok;
        {error, _} -> ok
    end.

% Same msg_type, but {ok, X} when is_atom(X) is always dead
%-etylizer({msg_type, stdlib_result_recv_02_fail, 0, "{ok, integer()} | {error, atom()}"}).
-spec stdlib_result_recv_02_fail() -> ok.
stdlib_result_recv_02_fail() ->
    receive
        {ok, X} when is_atom(X) -> ok;
        {error, _}              -> ok
    end.

%%%%%%%%%%%%%%%%%%%%%%%% NESTED pid(T) %%%%%%%%%%%%%%%%%%%%%%%

% Send a pid(integer()) to a pid(pid(integer()))
-spec nested_pid_send_01(pid(pid(integer())), pid(integer())) -> pid(integer()).
nested_pid_send_01(Relay, Worker) ->
    Relay ! Worker.

% Send an integer() to a pid(pid(integer()))
-spec nested_pid_send_02_fail(pid(pid(integer())), integer()) -> integer().
nested_pid_send_02_fail(Relay, N) ->
    Relay ! N.

% receive pid(integer()), forward to pid(pid(integer()))
%-etylizer({msg_type, nested_relay_01, 1, "pid(integer())"}).
-spec nested_relay_01(pid(pid(integer()))) -> no_return().
nested_relay_01(Relay) ->
    receive Worker -> Relay ! Worker end,
    nested_relay_01(Relay).

% receive integer(), forward to pid(pid(integer()))
%-etylizer({msg_type, nested_relay_02_fail, 1, "integer()"}).
-spec nested_relay_02_fail(pid(pid(integer()))) -> no_return().
nested_relay_02_fail(Relay) ->
    receive N -> Relay ! N end,
    nested_relay_02_fail(Relay).

%%%%%%%%%%%%%%%%%%%%%%%% INTERSECTION MSG_TYPE %%%%%%%%%%%%%%%%%%%%%%%

% msg_type list arity = function arity.
% Desugared to a helper expression with case body and intersection spec.
% Component (1)->ok: case 1->ok active, Any->Any redundant (compare how intersections are handled in case_of.erl).
% Component (any())->any(): both branches active, returns any().
%-etylizer({msg_type, recv_inter_01, 1, [
%                           "fun((1) -> ok)", 
%                           "fun((any()) -> any())"
%                        ]}).
-spec recv_inter_01(1) -> ok; (any()) -> any().
recv_inter_01(_) ->
    receive 1 -> ok; Any -> Any end.


%% DESUGARED INTO (only for typing)
%% original function: receive replaced by direct call, params forwarded
% -spec recv_inter_01(1) -> ok; (any()) -> any().
% recv_inter_01(_RecvP_a) ->
%   '__recv__recv_inter_01__0'(_RecvP_a).
%
%% helper: intersection spec lifted from the msg_type list, receive cases become a case
% -spec '__recv__recv_inter_01__0'(1) -> ok; (any()) -> any().
% '__recv__recv_inter_01__0'(_RecvP_b) ->
%   case _RecvP_b of
%       1   -> ok;
%       Any -> Any
%   end.


% 0-arg function, 1-arg msg_type (open protocol).
% Component (integer())->atom(): scrutinee integer(), guard is_integer holds, returns foo
% Component (any())->any(): both branches active, returns atom()|any() = any()
%-etylizer({msg_type, recv_open_01, 0, [
%                           "fun((integer()) -> atom())", 
%                           "fun((any()) -> any())"
%                       ]}).
-spec recv_open_01() -> any().
recv_open_01() ->
    receive 
        X when is_integer(X) -> foo; 
        Other -> Other 
    end.


%% DESUGARED INTO (only for typing)
%% injected: pins the outer pass-through receive's message type to term() (top)
%-etylizer({msg_type, recv_open_01, 0, term()}).
%% original function: receive becomes an untyped pass-through that forwards the message
% -spec recv_open_01() -> term().
% recv_open_01() ->
%   receive
%       __RecvMsg -> '__recv__recv_open_01__0'(__RecvMsg)
%   end.

%% helper: takes the message as an extra param; receive cases become a case
% -spec '__recv__recv_open_01__0'(integer()) -> atom(); (term()) -> term().
% '__recv__recv_open_01__0'(__RecvP_c) ->
%   case __RecvP_c of
%       X when is_integer(X) -> foo;
%       Other               -> Other
%   end.

% Missing is_integer guard: case Other->Other with scrutinee integer() returns integer(),
% but component (integer())->atom() requires atom()
%-etylizer({msg_type, recv_open_02_fail, 0, ["fun((integer()) -> atom())", "fun((term()) -> term())"]}).
-spec recv_open_02_fail() -> atom().
recv_open_02_fail() ->
    receive Other -> Other end.
