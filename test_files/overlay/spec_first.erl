-module(spec_first).
-compile([export_all, nowarn_export_all]).

% the corrected spec, for the calls of first/1
-spec 'corrected:first'([atom(), ...]) -> atom().
'corrected:first'(_) -> error(overlay).
