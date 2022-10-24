-module(check_if_fail).

-compile(export_all).
-compile(nowarn_export_all).

-spec bar(integer() | string()) -> boolean().
bar(X) -> false.

-spec foo(integer() | string()) -> integer().
foo(X) ->
    B = bar(X),
    if
        B -> X + 1;
        X =:= "foo" -> -1;
        true -> 42
    end.
