-module(lib_last).
-compile([export_all, nowarn_export_all]).

-spec 'lists:last'(atom()) -> atom().
'lists:last'(_) -> error(overlay).
