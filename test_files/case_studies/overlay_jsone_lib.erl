-module(overlay_jsone_lib).
-compile([export_all, nowarn_export_all]).

% Library specs for jsone.

% OTP: Maximum :: term()
-spec 'erlang:max'(A, B) -> A | B.
'erlang:max'(_, _) -> error(overlay).

% OTP: (integer()) -> string(). The digits and the sign are bytes.
-spec 'erlang:integer_to_list'(integer()) -> [$- | $0..$9].
'erlang:integer_to_list'(_) -> error(overlay).
