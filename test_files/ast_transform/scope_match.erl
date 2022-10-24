-module(scope_match).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    {X, Y} = begin Y = 2, {1, 2} end,
    {X, Y}.
