-module(overlay_gb_sets).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of gb_sets.erl that have none upstream.

% Upstream types a node gb_set_node(E) :: nil | {E, _, _}, the subtrees are term().
-type tree(E) :: nil | {E, tree(E), tree(E)}.

-spec 'gb_sets:is_member_1'(E, tree(E)) -> boolean().
'gb_sets:is_member_1'(_, _) -> error(overlay).
-spec 'gb_sets:insert_1'(E, tree(E), integer()) -> tree(E) | {tree(E), integer(), non_neg_integer()}.
'gb_sets:insert_1'(_, _, _) -> error(overlay).
-spec 'gb_sets:count'(tree(_)) -> {integer(), non_neg_integer()}.
'gb_sets:count'(_) -> error(overlay).
-spec 'gb_sets:balance_unchecked'(tree(E), non_neg_integer()) -> tree(E).
'gb_sets:balance_unchecked'(_, _) -> error(overlay).
-spec 'gb_sets:balance_list_unchecked'([E], non_neg_integer()) -> tree(E).
'gb_sets:balance_list_unchecked'(_, _) -> error(overlay).
-spec 'gb_sets:balance_list_unchecked_1'([E], non_neg_integer()) -> {tree(E), [E]}.
'gb_sets:balance_list_unchecked_1'(_, _) -> error(overlay).
-spec 'gb_sets:balance_list_checked'([E], non_neg_integer()) -> tree(E).
'gb_sets:balance_list_checked'(_, _) -> error(overlay).
-spec 'gb_sets:balance_list_checked_1'([E], non_neg_integer()) -> {tree(E), [E]}.
'gb_sets:balance_list_checked_1'(_, _) -> error(overlay).
-spec 'gb_sets:from_ordset_unchecked'([E]) -> gb_sets:set(E).
'gb_sets:from_ordset_unchecked'(_) -> error(overlay).
-spec 'gb_sets:to_list_1'(tree(E)) -> [E].
'gb_sets:to_list_1'(_) -> error(overlay).
-spec 'gb_sets:to_list'(tree(E), [E]) -> [E].
'gb_sets:to_list'(_, _) -> error(overlay).
-spec 'gb_sets:union'([E], non_neg_integer(), tree(E), non_neg_integer()) -> gb_sets:set(E).
'gb_sets:union'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:union_1'([E], gb_sets:set(E)) -> gb_sets:set(E).
'gb_sets:union_1'(_, _) -> error(overlay).
-spec 'gb_sets:union_2'([E], [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:union_2'(_, _, _) -> error(overlay).
-spec 'gb_sets:union_2'([E], [E], [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:union_2'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:push'([E], [E]) -> [E].
'gb_sets:push'(_, _) -> error(overlay).
-spec 'gb_sets:balance_revlist'([E], non_neg_integer()) -> tree(E).
'gb_sets:balance_revlist'(_, _) -> error(overlay).
-spec 'gb_sets:balance_revlist_1'([E], non_neg_integer()) -> {tree(E), [E]}.
'gb_sets:balance_revlist_1'(_, _) -> error(overlay).
-spec 'gb_sets:intersection'([E], non_neg_integer(), tree(E), non_neg_integer()) -> gb_sets:set(E).
'gb_sets:intersection'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:intersection_1'([E], tree(E)) -> gb_sets:set(E).
'gb_sets:intersection_1'(_, _) -> error(overlay).
-spec 'gb_sets:intersection_1'([E], tree(E), [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:intersection_1'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:intersection_2'([E], [E]) -> gb_sets:set(E).
'gb_sets:intersection_2'(_, _) -> error(overlay).
-spec 'gb_sets:intersection_2'([E], [E], [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:intersection_2'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:intersection_list'(gb_sets:set(E), [gb_sets:set(E)]) -> gb_sets:set(E).
'gb_sets:intersection_list'(_, _) -> error(overlay).
-spec 'gb_sets:difference'([E], non_neg_integer(), tree(E), non_neg_integer()) -> gb_sets:set(E).
'gb_sets:difference'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:difference_1'([E], tree(E)) -> gb_sets:set(E).
'gb_sets:difference_1'(_, _) -> error(overlay).
-spec 'gb_sets:difference_1'([E], tree(E), [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:difference_1'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:difference_2'([E], [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:difference_2'(_, _, _) -> error(overlay).
-spec 'gb_sets:difference_2'([E], [E], [E], non_neg_integer()) -> gb_sets:set(E).
'gb_sets:difference_2'(_, _, _, _) -> error(overlay).
-spec 'gb_sets:fold_1'(fun((E, Acc) -> Acc), Acc, tree(E)) -> Acc.
'gb_sets:fold_1'(_, _, _) -> error(overlay).
-spec 'gb_sets:split_list_size'(pos_integer()) -> {non_neg_integer(), non_neg_integer()}.
'gb_sets:split_list_size'(_) -> error(overlay).
