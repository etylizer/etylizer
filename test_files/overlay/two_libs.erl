-module(two_libs).
-export([rev/0, last/0]).

% both fail with the specs of OTP
-spec rev() -> atom().
rev() -> lists:reverse(a).

-spec last() -> atom().
last() -> lists:last(a).
