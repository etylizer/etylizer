-module(spec_use).
-compile([export_all, nowarn_export_all]).

% use/0 has a spec in its module, this one applies to its calls
-spec 'unspecced:use'() -> atom().
'unspecced:use'() -> error(overlay).
