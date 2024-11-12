-module(test).

-compile(export_all).
-compile(nowarn_export_all).

-type exp() :: integer() | {add, exp(), exp()}.

-spec eval(exp()) -> integer().
eval(E) ->
    case E of
        {add, E1, E2} -> eval(E1) + eval(E2);
        _I -> 1
    end.
