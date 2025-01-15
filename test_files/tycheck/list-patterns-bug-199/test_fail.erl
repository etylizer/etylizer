-module(test_fail).

-compile(export_all).
-compile(nowarn_export_all).

-spec foo(nonempty_list()) -> ok.
foo([_ | _]) -> ok.

-spec tmp_dir2() -> integer().
tmp_dir2() ->
    Fun =
        fun _F(X) ->
            case X of
                [] -> 42;
                [_V | Vs] -> foo(Vs), 41 % should fail because Vs might be empty
            end
        end,
    Fun(["X"]) + Fun([]).
