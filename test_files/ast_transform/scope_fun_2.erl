-module(scope_fun).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    F = fun (X, X) -> X == X end,
    G = fun F(X, X) -> X == F(X, X) end,
    {F(X, X), G(X, X)}.
