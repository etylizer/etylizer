-module(overlay_jsone_lib).
-compile([export_all, nowarn_export_all]).

% Library specs for jsone.study.

% OTP: Maximum :: term()
-spec 'erlang:max'(A, B) -> A | B.
'erlang:max'(_, _) -> error(overlay).
