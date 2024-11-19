-module(test).

-compile(export_all).
-compile(nowarn_export_all).

-spec range(#{ any() => V }) -> [V].
range(Map) ->
    lists:map(fun({_, V}) -> V end, maps:to_list(Map))
