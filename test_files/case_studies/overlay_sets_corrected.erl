-module(overlay_sets_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of sets.erl: calls use them, the functions are checked against
% these and their specs upstream.

-spec 'sets:get_slot'(sets:set_v1(E), E) -> pos_integer().
'sets:get_slot'(_, _) -> error(overlay).
-spec 'sets:get_bucket'(sets:set_v1(Element), pos_integer()) -> [Element].
'sets:get_bucket'(_, _) -> error(overlay).
-spec 'sets:update_bucket'(sets:set_v1(E), pos_integer(), [E]) -> sets:set_v1(E).
'sets:update_bucket'(_, _, _) -> error(overlay).
