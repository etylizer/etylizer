-module(overlay_maps).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of maps.erl that have none upstream.

-type step(K, V) :: {K, V, maps:iterator(K, V)} | none.
-type tag() :: undefined | reference().

-spec 'maps:intersect_combiner_v1'(term(), V1, term()) -> V1.
'maps:intersect_combiner_v1'(_, _, _) -> error(overlay).
-spec 'maps:intersect_combiner_v2'(term(), term(), V2) -> V2.
'maps:intersect_combiner_v2'(_, _, _) -> error(overlay).
-spec 'maps:intersect_with_small_map_first'(fun((K, V1, V2) -> V3), #{K => V1}, #{term() => V2}) -> #{K => V3}.
'maps:intersect_with_small_map_first'(_, _, _) -> error(overlay).
-spec 'maps:intersect_with_iterate'(step(K, V1), [{K, V3}], #{term() => V2}, fun((K, V1, V2) -> V3)) -> #{K => V3}.
'maps:intersect_with_iterate'(_, _, _, _) -> error(overlay).
-spec 'maps:merge_with_1'(step(K2, V2), #{K1 | K2 => V1 | V2 | V3}, fun((K2, V1, V2) -> V3)) -> #{K1 | K2 => V1 | V2 | V3}.
'maps:merge_with_1'(_, _, _) -> error(overlay).
-spec 'maps:to_list_from_iterator'(step(K, V)) -> [{K, V}].
'maps:to_list_from_iterator'(_) -> error(overlay).
-spec 'maps:to_list_internal'([term()]) -> [term()].
'maps:to_list_internal'(_) -> error(overlay).
-spec 'maps:filter_1'(fun((K, V) -> boolean()), step(K, V), tag()) -> [{K, V}].
'maps:filter_1'(_, _, _) -> error(overlay).
-spec 'maps:filtermap_1'(fun((K, V1) -> boolean() | {true, V2}), step(K, V1), tag()) -> [{K, V1 | V2}].
'maps:filtermap_1'(_, _, _) -> error(overlay).
-spec 'maps:foreach_1'(fun((K, V) -> term()), step(K, V), tag()) -> ok.
'maps:foreach_1'(_, _, _) -> error(overlay).
-spec 'maps:fold_1'(fun((K, V, Acc) -> Acc), Acc, step(K, V), tag()) -> Acc.
'maps:fold_1'(_, _, _, _) -> error(overlay).
-spec 'maps:map_1'(fun((K, V1) -> V2), step(K, V1), tag()) -> [{K, V2}].
'maps:map_1'(_, _, _) -> error(overlay).
-spec 'maps:with_1'([K], #{K => V, term() => term()}) -> [{K, V}].
'maps:with_1'(_, _) -> error(overlay).
-spec 'maps:groups_from_list_1'(fun((E) -> K), [E], #{K => [E]}) -> #{K => [E]}.
'maps:groups_from_list_1'(_, _, _) -> error(overlay).
-spec 'maps:groups_from_list_2'(fun((E) -> K), fun((E) -> V), [E], #{K => [V]}) -> #{K => [V]}.
'maps:groups_from_list_2'(_, _, _, _) -> error(overlay).
-spec 'maps:error_type'(term()) -> badarg | {badmap, term()}.
'maps:error_type'(_) -> error(overlay).
-spec 'maps:error_type_two_maps'(term(), term()) -> {badmap, term()}.
'maps:error_type_two_maps'(_, _) -> error(overlay).
-spec 'maps:error_type_merge_intersect'(term(), term(), term()) -> badarg | {badmap, term()}.
'maps:error_type_merge_intersect'(_, _, _) -> error(overlay).
-spec 'maps:badarg_with_info'([term()]) -> none().
'maps:badarg_with_info'(_) -> error(overlay).
-spec 'maps:error_with_info'(term(), [term()]) -> none().
'maps:error_with_info'(_, _) -> error(overlay).
-spec 'maps:is_iterator_valid_1'(term()) -> true.
'maps:is_iterator_valid_1'(_) -> error(overlay).
-spec 'maps:try_next'(maps:iterator(K, V) | step(K, V), tag()) -> step(K, V).
'maps:try_next'(_, _) -> error(overlay).
