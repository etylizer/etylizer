-module(overlay_orddict).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of orddict.erl that have none upstream.

-spec 'orddict:take_1'(Key, orddict:orddict(Key, Value), [{Key, Value}]) -> error | {Value, orddict:orddict(Key, Value)}.
'orddict:take_1'(_, _, _) -> error(overlay).
-spec 'orddict:reverse_pairs'([{Key, Value}], [{Key, Value}]) -> [{Key, Value}].
'orddict:reverse_pairs'(_, _) -> error(overlay).
