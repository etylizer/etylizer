-module(filtermap_fail2).

-compile(export_all).
-compile(nowarn_export_all).

-spec my_filtermap(fun((T) -> boolean()), [T]) -> [T]
              ; (fun((T) -> {true, U} | false), [T]) -> [U]
              ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
my_filtermap(_F, []) -> [];
my_filtermap(F, [X|XS]) ->
    case F(X) of
        false -> my_filtermap(F, XS);
        true -> [X + 1 | my_filtermap(F, XS)]; % error here
        {true, Y} -> [Y | my_filtermap(F, XS)]
    end.
