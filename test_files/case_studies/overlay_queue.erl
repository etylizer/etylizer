-module(overlay_queue).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of queue.erl that have none upstream.

-spec 'queue:f2r'([Item]) -> queue:queue(Item).
'queue:f2r'(_) -> error(overlay).
-spec 'queue:r2f'([Item]) -> queue:queue(Item).
'queue:r2f'(_) -> error(overlay).
-spec 'queue:delete_with_rear'(Pred, R1) -> false | R2 when Pred :: fun((Item) -> boolean()), R1 :: [Item], R2 :: [Item], Item :: term().
'queue:delete_with_rear'(_, _) -> error(overlay).
-spec 'queue:delete_with_front'(Pred, Q1) -> false | Q2 when Pred :: fun((Item) -> boolean()), Q1 :: [Item], Q2 :: [Item], Item :: term().
'queue:delete_with_front'(_, _) -> error(overlay).
-spec 'queue:delete_rear'(Item, [Item]) -> false | [Item].
'queue:delete_rear'(_, _) -> error(overlay).
-spec 'queue:delete_front'(Item, [Item]) -> false | [Item].
'queue:delete_front'(_, _) -> error(overlay).
-spec 'queue:filtermap_r'(Fun, Q1) -> Q2 when Fun :: fun((Item) -> boolean() | {'true', Value}), Q1 :: list(Item), Q2 :: list(Item | Value), Item :: term(), Value :: term().
'queue:filtermap_r'(_, _) -> error(overlay).
-spec 'queue:filter_r'(Fun, Q1 :: list(Item)) -> Q2 :: list(Item) when Fun :: fun((Item) -> boolean() | list(Item)).
'queue:filter_r'(_, _) -> error(overlay).
-spec 'queue:filter_f'(Fun, Q1 :: list(Item)) -> Q2 :: list(Item) when Fun :: fun((Item) -> boolean() | list(Item)).
'queue:filter_f'(_, _) -> error(overlay).
-spec 'queue:split_r1_to_f2'(non_neg_integer(), [Item], [Item], [Item],[Item]) -> {queue:queue(Item), queue:queue(Item)}.
'queue:split_r1_to_f2'(_, _, _, _, _) -> error(overlay).
-spec 'queue:split_f1_to_r2'(non_neg_integer(), [Item], [Item], [Item], [Item]) -> {queue:queue(Item), queue:queue(Item)}.
'queue:split_f1_to_r2'(_, _, _, _, _) -> error(overlay).
