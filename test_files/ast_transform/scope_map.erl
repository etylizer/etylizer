-module(scope_map).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    M = #{begin Z = X, Z end => begin Y = 3, Z = 1, {Y, Z} end},
    _ = (begin A = 2, M end)#{begin B = 3, A = 2, X end => 1},
    {Y, Z, A, B}.
