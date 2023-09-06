-module(b_tuple).
-vsn({2,0,0}).

-type ty_tuple() :: term().
-type ty_ref() :: {ty_ref, integer()}.

-callback tuple(ty_ref(), ty_ref()) -> ty_tuple().
-callback pi1(ty_tuple()) -> ty_ref().
-callback pi2(ty_tuple()) -> ty_ref().

