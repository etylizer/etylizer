-module(overlay_queue_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% OTP: ([T], term()) -> [T], the tail is not in the result type.
-spec 'lists:reverse'([], Tail) -> Tail;
                     (nonempty_list(T), [U]) -> nonempty_list(T | U);
                     (list(T), [U]) -> list(T | U).
'lists:reverse'(_, _) -> error(overlay).
