-module(overlay_jsone).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

-spec 'jsone_decode:object_key'(jsone:json_string(), jsone_decode:opt()) -> binary() | atom().
'jsone_decode:object_key'(_, _) -> error(overlay).
