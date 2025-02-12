-module(filtermap).

-include_lib("eunit/include/eunit.hrl").

-spec my_filtermap(fun((T) -> boolean()), [T]) -> [T]
                ; (fun((T) -> {true, U} | false), [T]) -> [U]
                ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
my_filtermap(F, L) ->
    case L of
        [] -> [];
        [X|XS] -> 
            case F(X) of
                false -> my_filtermap(F, XS);
                true -> [X | my_filtermap(F, XS)];
                {true, Y} -> [Y | my_filtermap(F, XS)]
            end
    end.

