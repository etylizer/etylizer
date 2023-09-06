-module(prop_phi_tuple).
%%
%%-include_lib("proper/include/proper.hrl").
%%-include_lib("eunit/include/eunit.hrl").
%%-import(prop_subty, [limited_ast/0]).
%%
%%% v0 & v1 is exponentially slower than v2 & v3
%%% v2 and v3 roughly same time
%%
%%% Φ(S1 , S2 , ∅ , T1 , T2) = (S1<:T1) or (S2<:T2)
%%% Φ(S1 , S2 , N ∪ {T1, T2} , Left , Right) = Φ(S1 , S2 , N , Left | T1 , Right) and Φ(S1 , S2 , N , Left , Right | T2)
%%phi_v0(S1, S2, N) -> phi_v0(S1, S2, N, ty_rec:empty(), ty_rec:empty()).
%%phi_v0(S1, S2, [], T1, T2) ->
%%  ty_rec:is_subtype(S1, T1)
%%    orelse
%%    ty_rec:is_subtype(S2, T2);
%%phi_v0(S1, S2, [Ty | N], Left, Right) ->
%%  T1 = ty_tuple:pi1(Ty),
%%  T2 = ty_tuple:pi2(Ty),
%%
%%  (phi_v0(S1, S2, N, ty_rec:union(Left,T1), Right))
%%    andalso
%%    (phi_v0(S1, S2, N , Left, ty_rec:union(Right,T2))).
%%
%%
%%%invariant1: Φ(S1 , S2 , N , Left , Right) = Φ' (S1 \ Left , S2 \ Right , N)
%%phi_v1(S1, S2, []) ->
%%  ty_rec:is_empty(S1)
%%    orelse
%%    ty_rec:is_empty(S2);
%%phi_v1(S1, S2, [Ty | N]) ->
%%  T1 = ty_tuple:pi1(Ty),
%%  T2 = ty_tuple:pi2(Ty),
%%
%%  phi_v1(ty_rec:diff(S1, T1), S2, N)
%%    andalso
%%    phi_v1(S1, ty_rec:diff(S2, T2), N).
%%
%%phi_v2(S1, S2, []) ->
%%  ty_rec:is_empty(S1)
%%    orelse
%%    ty_rec:is_empty(S2);
%%phi_v2(S1, S2, [Ty | N]) ->
%%  T1 = ty_tuple:pi1(Ty),
%%  T2 = ty_tuple:pi2(Ty),
%%
%%  ty_rec:is_empty(S1)
%%    orelse ty_rec:is_empty(S2)
%%    orelse (
%%      phi_v2(ty_rec:diff(S1, T1), S2, N)
%%        andalso
%%        phi_v2(S1, ty_rec:diff(S2, T2), N)
%%  ).
%%
%%% from paper
%%phi_v3(_S1, _S2, []) ->
%%  false;
%%phi_v3(S1, S2, [Ty | N]) ->
%%  T1 = ty_tuple:pi1(Ty),
%%  T2 = ty_tuple:pi2(Ty),
%%
%%  (
%%      ty_rec:is_subtype(S1, T1)
%%        orelse
%%        phi_v3(ty_rec:diff(S1, T1), S2, N)
%%  )
%%  andalso
%%  (
%%      ty_rec:is_subtype(S2, T2)
%%        orelse
%%        phi_v3(S1, ty_rec:diff(S2, T2), N)
%%  ).
%%
%%prop_phi_invariant1() ->
%%  ?FORALL({S1, S2, N, T1, T2}, {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()}), limited_ast(), limited_ast()},
%%    begin
%%      NTuple = lists:map(fun({L, R}) -> ty_tuple:tuple(L, R) end, lists:sublist(N, 3)),
%%      phi_v0(S1, S2, NTuple, T1, T2) =:= phi_v1(ty_rec:diff(S1, T1), ty_rec:diff(S2, T2), NTuple)
%%    end
%%  ).
%%
%%prop_phi_invariant2() ->
%%  ?FORALL({Ty, N}, {limited_ast(), list({limited_ast(), limited_ast()})},
%%    begin
%%      NTuples = lists:map(fun({L, R}) -> ty_tuple:tuple(L, R) end, lists:sublist(N, 3)),
%%      true = phi_v1(ty_rec:empty(), Ty, NTuples),
%%      true = phi_v1(Ty, ty_rec:empty(), NTuples),
%%      true
%%    end
%%  ).
%%
%%prop_phi_equivalence() ->
%%  ?FORALL(
%%    {S1, S2, N},
%%    {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()})},
%%    begin
%%      PTuples = lists:map(fun({L, R}) -> ty_tuple:tuple(L, R) end, lists:sublist(N, 3)),
%%
%%      R1 = phi_v0(S1, S2, PTuples),
%%      R2 = phi_v1(S1, S2, PTuples),
%%      R3 = phi_v2(S1, S2, PTuples),
%%      R4 = (ty_rec:is_empty(S1) orelse ty_rec:is_empty(S2) orelse phi_v3(S1, S2, PTuples)),
%%
%%      R1 =:= R2
%%        andalso R1 =:= R3
%%        andalso R1 =:= R4
%%
%%    end
%%  ).
%%
%%
%%
%%%%prop_phi_timing() ->
%%%%  ?FORALL({T1, T2, P}, {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()})},
%%%%    begin
%%%%      PTuple = lists:map(fun({D, C}) -> ty_tuple:tuple(D, C) end, P),
%%%%
%%%%%%      {Ti1, R} = timer:tc(fun() -> phi_v0(T1, T2, PTuple) end),
%%%%%%      {Ti2, R} = timer:tc(fun() -> phi_v1(T1, T2, PTuple) end),
%%%%      {Tix, R} = timer:tc(fun() -> phi_v2(T1, T2, PTuple) end),
%%%%      {Tiy, R} = timer:tc(fun() -> (ty_rec:is_empty(T1) orelse ty_rec:is_empty(T2) orelse phi_v3(T1, T2, PTuple)) end),
%%%%
%%%%
%%%%      ty_ref:reset(),
%%%%      {Ti3, R} = timer:tc(fun() -> phi_v2(T1, T2, PTuple) end),
%%%%      ty_ref:reset(),
%%%%      {Ti4, R} = timer:tc(fun() -> (ty_rec:is_empty(T1) orelse ty_rec:is_empty(T2) orelse phi_v3(T1, T2, PTuple)) end),
%%%%      io:format(user, "~p :: {~p, ~p}~n", [R, Ti3/1000, Ti4/1000]),
%%%%
%%%%      true
%%%%    end
%%%%  ).
