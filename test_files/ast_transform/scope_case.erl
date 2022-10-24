-module(scope_case).

-compile(export_all).
-compile([nowarn_export_all, nowarn_shadow_vars]).

foo(X) ->
    case
        begin
            Y = 2,
            X
        end
    of
        A = 1 when Y == 2 -> Z = (A - 1);
        _ -> Z = 1, A = 3
    end,
    {A, Y, Z}.
