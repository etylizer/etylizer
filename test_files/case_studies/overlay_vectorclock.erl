%% Library specs for the vectorclock case study that overlay.erl does not have.
-module(overlay_vectorclock).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% OTP: min(Term1, Term2) -> Minimum, each of them a term()
-spec 'erlang:min'(A, B) -> A | B.
'erlang:min'(_, _) -> error(overlay).
