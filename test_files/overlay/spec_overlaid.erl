-module(spec_overlaid).
-compile([export_all, nowarn_export_all]).

% wrong for the body of first/1
-spec 'overlaid:first'([atom(), ...]) -> integer().
'overlaid:first'(_) -> error(overlay).
