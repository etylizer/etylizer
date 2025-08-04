-module(overlay_queue).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

-spec 'lists:reverse'
  (nonempty_list(T), term()) -> nonempty_list(T);
  (list(T), term()) -> list(T).
'lists:reverse'(_, _) -> error(overlay).
