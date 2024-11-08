-module(test).

-compile(export_all).
-compile(nowarn_export_all).

-type exp() :: integer()
             | {exp(), exp()}.

-spec eval(exp()) -> integer().
eval(E) ->
    case E of
        {E1, _E2} -> eval(E1);
        I -> I
    end.
