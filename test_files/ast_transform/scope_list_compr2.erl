-module(scope_list_compr2).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(Alts) ->
    [{S, A} || A <- Alts, S=A].

