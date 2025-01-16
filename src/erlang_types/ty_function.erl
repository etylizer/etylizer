-module(ty_function).

%% domain -> co-domain function representation
-export([compare/2, mu_equal/2, equal/2, all_variables/2, substitute/3]).
-export([function/2, domains/1, codomain/1, codomains_intersect/1, has_ref/2, transform/2, raw_transform/2]).

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.

mu_equal({{ty_function, C, D}, M1}, {{ty_function, C2, D2}, M2}) -> 
  length(C) == length(C2)
    andalso ty_rec:mu_eq({D, M1}, {D2, M2}) 
    andalso lists:all(fun({T1, T2}) -> ty_rec:mu_eq({T1, M1}, {T2, M2}) end, lists:zip(C, C2)).

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

raw_transform(T, Op) -> transform(T, Op).

substitute({ty_function, Refs, B}, Map, Memo) ->
    {ty_function,
        lists:map(fun(C) -> ty_rec:substitute(C, Map, Memo) end, Refs),
        ty_rec:substitute(B, Map, Memo)
    }.

all_variables({ty_function, Domain, Codomain}, M) ->
  ty_rec:all_variables(domains_to_tuple(Domain), M)
    ++ ty_rec:all_variables(Codomain, M).

domains_to_tuple(Domains) ->
    ty_rec:tuple(length(Domains), dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(Domains)))).
