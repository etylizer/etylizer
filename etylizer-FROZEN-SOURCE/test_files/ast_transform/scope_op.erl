-module(scope_op).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo() ->
    A = (begin B = 1, B end) + (begin C = 2, C end),
    {A, B, C}.
