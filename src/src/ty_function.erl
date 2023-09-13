-module(ty_function).

%% domain -> co-domain function representation

-behavior(eq).
-export([compare/2, equal/2]).

-behavior(b_function).
-export([function/2, domain/1, codomain/1, codomains_intersect/1, has_ref/2, transform/2]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

function(Ref1, Ref2) -> {ty_function, Ref1, Ref2}.

domain({ty_function, Ref, _}) -> Ref.
codomain({ty_function, _, Ref}) -> Ref.

codomains_intersect([]) -> ty_rec:any();
codomains_intersect([Fun]) -> ty_function:codomain(Fun);
codomains_intersect([Fun | Funs]) -> ty_rec:intersect(ty_function:codomain(Fun), codomains_intersect(Funs)).

has_ref({ty_function, Ref, _}, Ref) -> true;
has_ref({ty_function, _, Ref}, Ref) -> true;
has_ref({ty_function, _, _}, _Ref) -> false.

transform({ty_function, Ref1, Ref2}, #{to_fun := Fun}) ->
    Fun(Ref1, Ref2).



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
    TIa = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),
    TIb = ty_rec:interval(dnf_var_int:int(ty_interval:interval('*', '*'))),

    % int -> int
    _TyFunction = ty_function:function(TIa, TIb),

    ok.

-endif.
