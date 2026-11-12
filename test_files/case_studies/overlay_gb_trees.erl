-module(overlay_gb_trees).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of gb_trees.erl that have none upstream.

-spec 'gb_trees:lookup_1'(K, gb_trees:gb_tree_node(K, V)) -> none | {value, V}.
'gb_trees:lookup_1'(_, _) -> error(overlay).
-spec 'gb_trees:get_1'(K, gb_trees:gb_tree_node(K, V)) -> V.
'gb_trees:get_1'(_, _) -> error(overlay).
-spec 'gb_trees:update_1'(K, V, gb_trees:gb_tree_node(K, V)) -> gb_trees:gb_tree_node(K, V).
'gb_trees:update_1'(_, _, _) -> error(overlay).
-spec 'gb_trees:insert_1'(K, V, gb_trees:gb_tree_node(K, V), integer()) ->
          gb_trees:gb_tree_node(K, V) | {gb_trees:gb_tree_node(K, V), integer(), non_neg_integer()}.
'gb_trees:insert_1'(_, _, _, _) -> error(overlay).
-spec 'gb_trees:count'(gb_trees:gb_tree_node(_, _)) -> {integer(), non_neg_integer()}.
'gb_trees:count'(_) -> error(overlay).
-spec 'gb_trees:balance'(gb_trees:gb_tree_node(K, V), non_neg_integer()) -> gb_trees:gb_tree_node(K, V).
'gb_trees:balance'(_, _) -> error(overlay).
-spec 'gb_trees:balance_list_unchecked'([{K, V}], non_neg_integer()) -> gb_trees:gb_tree_node(K, V).
'gb_trees:balance_list_unchecked'(_, _) -> error(overlay).
-spec 'gb_trees:balance_list_unchecked_1'([{K, V}], non_neg_integer()) -> {gb_trees:gb_tree_node(K, V), [{K, V}]}.
'gb_trees:balance_list_unchecked_1'(_, _) -> error(overlay).
-spec 'gb_trees:to_list_1'(gb_trees:gb_tree_node(K, V)) -> [{K, V}].
'gb_trees:to_list_1'(_) -> error(overlay).
-spec 'gb_trees:to_list'(gb_trees:gb_tree_node(K, V), [{K, V}]) -> [{K, V}].
'gb_trees:to_list'(_, _) -> error(overlay).
-spec 'gb_trees:split_list_size'(pos_integer()) -> {non_neg_integer(), non_neg_integer()}.
'gb_trees:split_list_size'(_) -> error(overlay).
