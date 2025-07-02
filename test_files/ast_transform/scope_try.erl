-module(scope_try).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

use(_X) -> ok.

foo(X) ->
    try
        begin
            Y = 2,
            X
        end
    of
        1 -> Z = Y, use(Z);
        _ -> Z = 0, use(Z)
    catch
        % Y is unsafe here
        _ -> Z = 0, use(Z)
    after
        % Y, Z are unsafe here
        A = 3, use(A)
    end,
    % Y, Z, A are all unsafe
    ok.
