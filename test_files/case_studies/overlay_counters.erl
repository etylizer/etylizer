-module(overlay_counters).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of counters.erl that have none upstream.

-spec 'counters:error_with_info'(term(), [term()]) -> no_return().
'counters:error_with_info'(_, _) -> error(overlay).
