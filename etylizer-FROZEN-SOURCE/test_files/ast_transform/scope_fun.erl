-module(scope_fun).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    F = fun (X) -> X == X end,
    G = fun F(X) -> X == F(X) end,
    {F(X), G(X)}.
