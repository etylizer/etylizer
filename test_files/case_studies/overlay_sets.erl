-module(overlay_sets).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of sets.erl that have none upstream.

% A segment is always mk_seg(16), upstream types it seg() :: tuple().
-type seg(E) :: {[E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E], [E]}.

-spec 'sets:canonicalize_v2'(sets:set(Element)) -> sets:set(Element).
'sets:canonicalize_v2'(_) -> error(overlay).
-spec 'sets:is_disjoint_1'(map(), maps:iterator(_Element, [])) -> boolean().
'sets:is_disjoint_1'(_, _) -> error(overlay).
-spec 'sets:is_subset_1'(map(), maps:iterator(_Element, [])) -> boolean().
'sets:is_subset_1'(_, _) -> error(overlay).
-spec 'sets:fold_1'(fun((Element, Acc) -> Acc), Acc, maps:iterator(Element, [])) -> Acc.
'sets:fold_1'(_, _, _) -> error(overlay).
-spec 'sets:fold_set'(fun((_Element, Acc) -> Acc), Acc, sets:set_v1(_)) -> Acc.
'sets:fold_set'(_, _, _) -> error(overlay).
-spec 'sets:fold_bucket'(fun((Element, Acc) -> Acc), Acc, [Element]) -> Acc.
'sets:fold_bucket'(_, _, _) -> error(overlay).
-spec 'sets:filter_bucket'(fun((Element) -> boolean()), [Element], [Element], non_neg_integer()) -> {[Element], non_neg_integer()}.
'sets:filter_bucket'(_, _, _, _) -> error(overlay).
-spec 'sets:put_bucket_s'(sets:segs(Element), pos_integer(), [Element]) -> sets:segs(Element).
'sets:put_bucket_s'(_, _, _) -> error(overlay).
-spec 'sets:intersection_heuristic'({Element, [], maps:iterator(Element, [])} | none, [Element], [Element], integer(), #{Element => []}, #{Element => []}) -> #{Element => []}.
'sets:intersection_heuristic'(_, _, _, _, _, _) -> error(overlay).
-spec 'sets:intersection_decided'({Element, [], maps:iterator(Element, [])} | none, #{Element => V}, #{Element => V}) -> #{Element => V}.
'sets:intersection_decided'(_, _, _) -> error(overlay).
-spec 'sets:remove_keys'([Element], #{Element => V}) -> #{Element => V}.
'sets:remove_keys'(_, _) -> error(overlay).
-spec 'sets:subtract_heuristic'({Element, [], maps:iterator(Element, [])} | none, [Element], [Element], integer(), #{Element => []}, #{Element => []}) -> #{Element => []}.
'sets:subtract_heuristic'(_, _, _, _, _, _) -> error(overlay).
-spec 'sets:subtract_decided'({K, [], maps:iterator(K, [])} | none, #{K => []}, #{K => []}) -> #{K => []}.
'sets:subtract_decided'(_, _, _) -> error(overlay).
-spec 'sets:fold_segs'(fun((Element, Acc) -> Acc), Acc, sets:segs(Element), non_neg_integer()) -> Acc.
'sets:fold_segs'(_, _, _, _) -> error(overlay).
-spec 'sets:fold_seg'(fun((Element, Acc) -> Acc), Acc, seg(Element), non_neg_integer()) -> Acc.
'sets:fold_seg'(_, _, _, _) -> error(overlay).
-spec 'sets:filter_set'(fun((E) -> boolean()), sets:set_v1(E)) -> sets:set(E).
'sets:filter_set'(_, _) -> error(overlay).
-spec 'sets:filter_seg_list'(fun((Element) -> boolean()), [seg(Element)], [sets:seg()], non_neg_integer()) -> {[sets:seg()], non_neg_integer()}.
'sets:filter_seg_list'(_, _, _, _) -> error(overlay).
-spec 'sets:filter_bkt_list'(fun((Element) -> boolean()), [[Element]], [[Element]], non_neg_integer()) -> {[[Element]], non_neg_integer()}.
'sets:filter_bkt_list'(_, _, _, _) -> error(overlay).
-spec 'sets:get_bucket_s'(sets:segs(Element), pos_integer()) -> [Element].
'sets:get_bucket_s'(_, _) -> error(overlay).
