-module(overlay_queue_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of queue.erl: calls use them, the functions are checked against
% these and their specs upstream.

-spec 'queue:get'([Item], [Item, ...]) -> Item; ([Item, ...], []) -> Item; ([], []) -> none().
'queue:get'(_, _) -> error(overlay).
