-module(range1).

-compile(export_all).
-compile(nowarn_export_all).

-spec to_list(#{Key => Value}) -> [{Key, Value}].
to_list(X) -> to_list(X).

-spec range(#{ any() => V }) -> [V].
range(Map) ->
    lists:map(fun({_, V}) -> V end, to_list(Map)).
