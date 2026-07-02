-module(test2).

-compile(export_all).
-compile(nowarn_export_all).

-spec f(list()) -> string().
f([]) -> ".";
f([_V | Vs]) -> f(Vs).

-spec tmp_dir() -> string().
tmp_dir() ->
    f(["X"]).
