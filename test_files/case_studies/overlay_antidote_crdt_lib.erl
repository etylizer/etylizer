%% Library specs for the antidote_crdt case study (antidote_crdt.study): functions of OTP whose spec says
%% too little for the checker. Each spec is true for every call that it admits; none says more than the
%% function does. An overlay spec replaces the spec that OTP has.
-module(overlay_antidote_crdt_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% OTP: ([number()]) -> number(). The sum of integers is an integer, the sum of the empty list is 0.
-spec 'lists:sum'([integer()]) -> integer();
                 ([number()]) -> number().
'lists:sum'(_) -> error(overlay).

%% OTP: (Key, Dict) -> {ok, Value} | error when Dict :: dict:dict(Key, Value). The parameters of
%% dict:dict(Key, Value) are not in its representation (segs(_Key, _Value) :: tuple()), so nothing binds
%% Value for the checker: it fits every type, and a branch on the result is reported as dead. Here the
%% value is a term().
-spec 'dict:find'(term(), dict:dict()) -> {ok, term()} | error.
'dict:find'(_, _) -> error(overlay).
