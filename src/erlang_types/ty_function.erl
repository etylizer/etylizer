-module(ty_function).

%% domain -> co-domain function representation
-export([compare/2, equal/2, all_variables/1, substitute/3]).
-export([function/2, domains/1, codomain/1, codomains_intersect/1, has_ref/2, transform/2]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

equal(P1, P2) -> compare(P1, P2) =:= 0.

function(Refs, Ref2) ->
    case Refs of
        _ when not is_list(Refs) -> error(Refs);
        _ -> ok
    end,
    true = is_list(Refs),
    {ty_function, Refs, Ref2}.

domains({ty_function, Refs, _}) ->
    true = is_list(Refs),
    Refs.
codomain({ty_function, _, Ref}) -> Ref.

codomains_intersect([]) -> ty_rec:any();
codomains_intersect([Fun]) -> ty_function:codomain(Fun);
codomains_intersect([Fun | Funs]) -> ty_rec:intersect(ty_function:codomain(Fun), codomains_intersect(Funs)).

has_ref({ty_function, _, Ref}, Ref) -> true;
has_ref({ty_function, Refs, _}, Ref) -> lists:member(Ref, Refs).

transform({ty_function, Ref1, Ref2}, #{to_fun := Fun}) ->
    Fun(Ref1, Ref2).

substitute({ty_function, Refs, B}, Map, Memo) ->
    {ty_function,
        lists:map(fun(C) -> ty_rec:substitute(C, Map, Memo) end, Refs),
        ty_rec:substitute(B, Map, Memo)
    }.

all_variables({ty_function, Domain, Codomain}) ->
  ty_rec:all_variables(dnf_ty_function:domains_to_tuple(Domain))
    ++ ty_rec:all_variables(Codomain).
