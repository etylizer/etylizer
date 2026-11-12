-module(overlay_maps_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of maps.erl: calls use them, the functions are checked against
% these and their specs upstream.

% OTP: ([{Key, Value}]) -> map()
-spec 'maps:from_list'([{K, V}]) -> #{K => V}.
'maps:from_list'(_) -> error(overlay).
% OTP: (Key, Value, map()) -> map(); K may hold more keys than the one put
-spec 'maps:put'(K, V, #{K1 => V1}) -> #{K | K1 => V | V1}.
'maps:put'(_, _, _) -> error(overlay).
% OTP: Init :: term() and the result AccOut, but an empty map gives Init
-spec 'maps:fold'(fun((K, V, Acc0 | Acc) -> Acc), Acc0, #{K => V} | maps:iterator(K, V)) -> Acc0 | Acc.
'maps:fold'(_, _, _) -> error(overlay).
% OTP: -> #{Key := Group}, but an empty list gives #{}
-spec 'maps:groups_from_list'(fun((E) -> K), fun((E) -> V), [E]) -> #{K => [V]}.
'maps:groups_from_list'(_, _, _) -> error(overlay).
% OTP: (Key, Fun, #{Key := Value1, _ => _}) -> #{Key := Value2, _ => _}: for a Key type of more
% than one key, the other keys of that type keep Value1
-spec 'maps:update_with'(K, fun((V1) -> V2), #{K1 => V1}) -> #{K | K1 => V1 | V2}.
'maps:update_with'(_, _, _) -> error(overlay).
% OTP: -> #{Key := Value2 | Init, _ => _}: the same
-spec 'maps:update_with'(K, fun((V1) -> V2), I, #{K1 => V1}) -> #{K | K1 => V1 | V2 | I}.
'maps:update_with'(_, _, _, _) -> error(overlay).
% OTP: -> #{Key1 => CombineResult, Key1 => Value1, Key2 => Value2}: the leftmost association
% takes precedence, keys of Map1 only keep Value1, keys of Map2 can be of type Key1
-spec 'maps:merge_with'(fun((K1, V1, V2) -> V3), #{K1 => V1}, #{K2 => V2}) -> #{K1 | K2 => V1 | V2 | V3}.
'maps:merge_with'(_, _, _) -> error(overlay).
% OTP: (Key, Value, #{Key := _, _ => _}) -> #{Key := Value, _ => _}: the same as update_with/3
-spec 'maps:update'(K, V, #{K1 => V1}) -> #{K | K1 => V | V1}.
'maps:update'(_, _, _) -> error(overlay).
