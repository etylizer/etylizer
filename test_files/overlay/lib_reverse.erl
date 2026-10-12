-module(lib_reverse).
-compile([export_all, nowarn_export_all]).

-spec 'lists:reverse'(atom()) -> atom().
'lists:reverse'(_) -> error(overlay).
