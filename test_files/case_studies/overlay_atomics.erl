-module(overlay_atomics).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of atomics.erl that have none upstream.

-spec 'atomics:encode_opts'([{signed, boolean()}], non_neg_integer()) -> non_neg_integer().
'atomics:encode_opts'(_, _) -> error(overlay).
-spec 'atomics:error_with_info'(term(), [term()]) -> no_return().
'atomics:error_with_info'(_, _) -> error(overlay).
