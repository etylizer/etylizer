-module(overlay_maps_lib).
-compile([export_all, nowarn_export_all]).

% Library specs for maps.erl.

% OTP: (non_neg_integer() | list(), map(), iterator | list()) -> {K, V, maps:iterator()} | list();
% with iterator the result can be none.
-spec 'erts_internal:map_next'(non_neg_integer() | list(), #{K => V}, iterator) -> {K, V, maps:iterator(K, V)} | none;
                              (non_neg_integer() | list(), map(), list()) -> list().
'erts_internal:map_next'(_, _, _) -> error(overlay).

% OTP: AccIn, AccOut, Acc0 and Acc1 :: term() are independent type variables
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).
