-module(spec_inc).
-compile([export_all, nowarn_export_all]).

-spec 'unspecced:inc'(integer()) -> integer().
'unspecced:inc'(_) -> error(overlay).
