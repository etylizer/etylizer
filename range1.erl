-module(range1).

-compile(export_all).
-compile(nowarn_export_all).


-spec range_fast(#{ _K => V }) -> [V].
range_fast(Map) ->
    lists:map(fun({_, V}) -> V end, maps:to_list(Map)).

-spec range({string(), #{ _K => V }}) -> [V].
range({_, Map}) ->
    lists:map(fun({_, V}) -> V end, maps:to_list(Map)).
