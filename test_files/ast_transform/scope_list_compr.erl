-module(scope_list_compr).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    [begin Y = X, X end || X <- [1,2,3,X], X > 3].
    % Y not bound here

