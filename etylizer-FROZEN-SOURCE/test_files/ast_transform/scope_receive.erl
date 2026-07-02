-module(scope_receive).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo() ->
    receive
        {From, 1} -> Z = 0;
        {From, _} -> Z = 1
    after begin
        Y = 2,
        Y + 8
        end ->
        Z = 2,
        From = none
    end,
    io:format("got ~w in foo, Y=~w~n", [Z, Y]),
    case From of
        none -> ok;
        Pid -> Pid ! Z
    end,
    foo().

% test() ->
%     Pid = spawn(fun foo/0),
%     Pid ! {self(), 1},
%     Pid ! {self(), 0},
%     io:format("receiving first answer~n"),
%     receive
%         X -> ok
%     end,
%     io:format("receiving second answer~n"),
%     receive
%         Y -> ok
%     end,
%     {X, Y}.
