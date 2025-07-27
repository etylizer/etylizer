-module(lists_overlay).

-compile(export_all).
-compile(nowarn_export_all).

%This requires using an overlay module like eqwalizer_spec.erl which overlays the current stdlib type for lists.

-spec loc_exp(exp()) -> loc().
loc_exp(X) -> element(2, X).`
