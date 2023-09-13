-module(ty_tuple).

%% n-tuple representation

-behavior(eq).
-export([compare/2, equal/2]).

-export([tuple/1, pi/2, has_ref/2, components/1, transform/2]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

tuple(Refs) -> {ty_tuple, Refs}.

components({ty_tuple, Refs}) -> Refs.
pi(I, {ty_tuple, Refs}) -> lists:nth(I, Refs).
has_ref({ty_tuple, Refs}, Ref) -> length([X || X <- Refs, X == Ref]) > 0.

transform({ty_tuple, Refs}, #{to_tuple := ToTuple}) ->
    ToTuple(Refs).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    % (int, int)
    TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),

    _Ty_Tuple = ty_tuple:tuple([TIa, TIb]),

    ok.

-endif.
