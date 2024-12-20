-module(lists_overlay).

-compile(export_all).
-compile(nowarn_export_all).

%This requires using an overlay module like eqwalizer_spec.erl which overlays the current stdlib type for lists.

-spec with_index([A]) -> [{integer(), A}].
with_index(L) -> with_index(0, L).

-spec with_index(integer(), [A]) -> [{integer(), A}].
with_index(Start, L) ->
    {_, Rev} = lists:foldl(fun (X, {I, Acc}) -> {I + 1, [{I, X} | Acc]} end,
                           {Start, []}, L),
    lists:reverse(Rev).
