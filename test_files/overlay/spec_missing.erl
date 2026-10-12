-module(spec_missing).
-compile([export_all, nowarn_export_all]).

-spec 'unspecced:no_such_function'(integer()) -> integer().
'unspecced:no_such_function'(_) -> error(overlay).
