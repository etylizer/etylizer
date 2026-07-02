-module(scope_if).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    if
        X == 1 -> A = 1;
        true -> A = 2
    end,
    A.
