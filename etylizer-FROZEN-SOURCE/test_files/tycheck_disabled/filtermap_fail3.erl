-module(filtermap_fail3).

-compile(export_all).
-compile(nowarn_export_all).

-spec my_filtermap(fun((T) -> boolean()), [T]) -> [T]
              ; (fun((T) -> {true, U} | false), [T]) -> [U]
              ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
my_filtermap(_F, []) -> [];
my_filtermap(F, [X|XS]) ->
    case F(X) of
        false -> my_filtermap(F, XS);
        true -> [X | my_filtermap(F, XS)];
        {true, Y} -> [Y+1 | my_filtermap(F, XS)] % error here
    end.
