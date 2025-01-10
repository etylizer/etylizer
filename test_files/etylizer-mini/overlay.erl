-module(overlay).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

-spec 'string:find' (string(), string(), string:direction()) -> string() | nomatch.
'string:find'(_, _, _) -> error(overlay).

-spec 'string:replace' (string(), string(), string()) -> [string()].
'string:replace'(_, _, _) -> error(overlay).

-spec 'string:replace' (string(), string(), string(), string:direction() | all) -> [string()].
'string:replace'(_, _, _, _) -> error(overlay).

-spec 'filename:join'([string()]) -> string().
'filename:join'(_) -> error(overlay).

-spec 'filename:join'(string(), string()) -> string().
'filename:join'(_, _) -> error(overlay).
