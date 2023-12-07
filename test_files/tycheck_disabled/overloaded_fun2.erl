-module(overloaded_fun2).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% ast_transform:trans_exp is similar: it transforms ast_erl:exp() into ast:exp() and
% ast_erl:guard() into ast:guard(), where guards are a subset of expressions.
% cduce typechecks this example successfully, see design/examples-cduce/overloaded_fun.cd
% gradualizer cannot handle this example.
-spec foo(integer()) -> integer();
          (1|2) -> (1|2).
foo(X) ->
    case X of
        1 -> 2;
        2 -> 1;
        _ -> X + 1
    end.

my_test() ->
    ?assertEqual(2, foo(1)),
    ?assertEqual(1, foo(2)),
    ?assertEqual(4, foo(3)).
