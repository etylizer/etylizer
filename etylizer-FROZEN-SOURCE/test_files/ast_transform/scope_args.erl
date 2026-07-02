-module(scope_args).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

bar(X) -> X + 1.

foo() ->
    bar(begin X = 1, X end),
    X.
