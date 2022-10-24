-module(patterns).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    case X of
        {Y, Y} -> Y; % the second Y in the {Y, Y} patterns refers to the first occurrence of Y
        {Y, Z} -> Y + lists:map(fun(Z) -> Z + 1 end, Z); % The parameter Z shadows the outer Z
        #{X := V, blub := {K, V}} -> K
    end.

bar(X) ->
    Y = X,
    Y = 3.

% The X in the second generator shadows the X of the first generator
spam() -> [X || X <- [1,2,3], X <- [4,5,X]].

catch_test() ->
    try throw(throw)
    % The second occurrence of X refers to the first
    catch X:X:_S -> ok end. % stacktrace variable '_S' must not be previously bound
