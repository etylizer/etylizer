-module(ty_tuple).

%% n-tuple representation
-export([compare/2, equal/2, substitute/3, all_variables/2]).

-export([tuple/1, pi/2, has_ref/2, components/1, raw_transform/2, transform/2, any/1, empty/1, big_intersect/1]).

empty(Size) -> {ty_tuple, Size, [ty_rec:empty() || _ <- lists:seq(1, Size)]}.
any(Size) -> {ty_tuple, Size, [ty_rec:any() || _ <- lists:seq(1, Size)]}.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

tuple(Refs) -> {ty_tuple, length(Refs), Refs}.

components({ty_tuple, _, Refs}) -> Refs.
pi(I, {ty_tuple, _, Refs}) -> lists:nth(I, Refs).
has_ref({ty_tuple, _, Refs}, Ref) -> length([X || X <- Refs, X == Ref]) > 0.

raw_transform(T, Op) -> transform(T, Op).
transform({ty_tuple, _, Refs}, #{to_tuple := ToTuple}) ->
    ToTuple(Refs).

big_intersect([]) -> error(illegal_state);
big_intersect([X]) -> X;
big_intersect([X | Y]) ->
    lists:foldl(fun({ty_tuple, _, Refs}, {ty_tuple, Dim, Refs2}) ->
        true = length(Refs) == length(Refs2),
        {ty_tuple, Dim, [ty_rec:intersect(S, T) || {S, T} <- lists:zip(Refs, Refs2)]}
                end, X, Y).

substitute({ty_tuple, Dim, Refs}, Map, Memo) ->
    {ty_tuple, Dim, [ ty_rec:substitute(B, Map, Memo) || B <- Refs ] }.

all_variables({ty_tuple, _, Refs}, M) ->
    lists:flatten([ty_rec:all_variables(E, M) || E <- Refs]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    % (int, int)
    TIa = ty_rec:interval(dnf_var_ty_interval:int(dnf_ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_ty_interval:int(dnf_ty_interval:interval('*', '*'))),

    _Ty_Tuple = ty_tuple:tuple([TIa, TIb]),

    ok.

-endif.
