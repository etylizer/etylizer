-module(range3).

-compile(export_all).
-compile(nowarn_export_all).

%-spec to_list(#{Key => Value}) -> [{Key, Value}].
-spec to_list(MapOrIterator) -> [{Key, Value}] when MapOrIterator :: #{Key => Value}.
to_list(X) -> to_list(X).

-spec map(Fun, List1) -> List2 when
      Fun :: fun((A) -> B),
      List1 :: [A],
      List2 :: [B].
map(F, L) -> map(F, L).

-spec range(#{ any() => A }) -> [A].
range(Map) ->
    map(
        fun (X) ->
            case X of
                {_, V} -> V
            end
        end,
        to_list(Map)).
