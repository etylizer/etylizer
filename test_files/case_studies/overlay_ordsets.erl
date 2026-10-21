-module(overlay_ordsets).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of ordsets.erl that have none upstream.

-spec 'ordsets:is_set'(list(term()), term()) -> boolean().
'ordsets:is_set'(_, _) -> error(overlay).
-spec 'ordsets:intersection1'(ordsets:ordset(_), [ordsets:ordset(_)]) -> ordsets:ordset(_).
'ordsets:intersection1'(_, _) -> error(overlay).
