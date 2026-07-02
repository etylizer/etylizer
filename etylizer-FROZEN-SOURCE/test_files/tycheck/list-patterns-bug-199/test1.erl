-module(test1).

-compile(export_all).
-compile(nowarn_export_all).

-spec tmp_dir() -> string().
tmp_dir() ->
    F =
        fun F([]) -> ".";
            F([_V | Vs]) -> F(Vs)
    end,
    F(["X"]).
