-module(impossible_branch_01).
% Bug #36

-compile(export_all).
-compile(nowarn_export_all).

-spec g(a) -> c; (b) -> d.
g(a) -> c;
g(b) -> d.

-spec f4(a) -> 1; (b) -> 2.
f4(X) ->
    case g(X) of
        c -> 1;
        d -> 2
    end.
