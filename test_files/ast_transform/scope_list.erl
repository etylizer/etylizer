-module(scope_list).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo() ->
    T = [A = 2, B = 3],
    {T, A, B}.
