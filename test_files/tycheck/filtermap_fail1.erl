-module(filtermap_fail1).

-compile(export_all).
-compile(nowarn_export_all).

-spec my_filtermap(fun((T) -> boolean()), [T]) -> [T]
                ; (fun((T) -> {true, _U} | false), [T]) -> [T]  % T instead of U
                ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
my_filtermap(_F, []) -> [];
my_filtermap(F, [X|XS]) ->
    case F(X) of
        false -> my_filtermap(F, XS);
        true -> [X | my_filtermap(F, XS)];
        {true, Y} -> [Y | my_filtermap(F, XS)]
    end.
