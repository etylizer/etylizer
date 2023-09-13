-module(b_interval).

-callback interval(integer() | '*', integer() | '*') -> term().
-callback cointerval(integer() | '*', integer() | '*') -> term().

