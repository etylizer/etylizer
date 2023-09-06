-module(prop_phi_function).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").
-import(prop_subty, [limited_ast/0]).

-export([phi_v0/3]).

% current state:
% v0, v1 and v2a are exponentially slower than v2b and v3
% v2b is fastest on average
% v3 (:= v2a + v2b) is sometimes faster by a constant factor (max 2x), but on average slower by a constant factor ~0.5x


% phi from paper covariance and contravariance
% phi(T1, T2, P0, P+, P-)
phi_v0(T1, T2, P) -> phi_v0(T1, T2, P, ty_rec:empty(), ty_rec:any()).
phi_v0(T1, T2, [], D , C) ->
  % (T1 <: D) or (C <: T2)
  ty_rec:is_subtype(T1, D) orelse ty_rec:is_subtype(C, T2);
% phi(T1, T2, P U {S1 --> S2}, D, C)
phi_v0(T1, T2, [Function | P], D, C) ->
  S1 = ty_function:domain(Function),
  S2 = ty_function:codomain(Function),
  % phi(T1, T2, P, D, C&S2)
  phi_v0(T1, T2, P, D, ty_rec:intersect(C, S2))
    andalso % and
    % phi(T1, T2, P, D|S1, C)
    phi_v0(T1, T2, P, ty_rec:union(D, S1), C).


% phi' (4.10) from paper covariance and contravariance
phi_v1(T1, T2, []) ->
  % phi'(Empty, T2, ∅) = true
  ty_rec:is_empty(T1)
    orelse
    % phi'(T1, Empty, ∅) = true
    ty_rec:is_empty(T2);
% phi'(T1, T2, ∅) = false
% phi'(T1, T2, P U {S1 --> S2}) = false
phi_v1(T1, T2, [Function | P]) ->
  S1 = ty_function:domain(Function),
  S2 = ty_function:codomain(Function),

  % phi'(T1, T2&S2, P)
  phi_v1(T1, ty_rec:intersect(T2, S2), P)
    andalso % and
    % phi'(T1\S1, T2, P)
    phi_v1(ty_rec:diff(T1, S1), T2, P).

% phi' optimization from paper
-spec phi_v2a(term(), term(), [term()]) -> boolean().
phi_v2a(T1, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(T1);
phi_v2a(T1, T2, [Function | P]) ->
  begin
    S1 = ty_function:domain(Function),
    S2 = ty_function:codomain(Function),
    (ty_rec:is_subtype(T1, S1) orelse ty_rec:is_subtype(ty_function:codomains_intersect(P), ty_rec:negate(T2)) )
      andalso
      phi_v2a(T1, ty_rec:intersect(T2, S2), P)
      andalso
      phi_v2a(ty_rec:diff(T1, S1), T2, P)
  end.

phi_v2b(T1, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(T1);
phi_v2b(T1, T2, [Function | P]) ->
  ty_rec:is_empty(T1) orelse ty_rec:is_empty(T2)
    orelse
    begin
      S1 = ty_function:domain(Function),
      S2 = ty_function:codomain(Function),
      phi_v2b(T1, ty_rec:intersect(T2, S2), P)
        andalso
        phi_v2b(ty_rec:diff(T1, S1), T2, P)
    end.

-spec phi_v3(term(), term(), [term()]) -> boolean().
phi_v3(T1, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(T1);
phi_v3(T1, T2, [Function | P]) ->
  ty_rec:is_empty(T1) orelse ty_rec:is_empty(T2)
    orelse
    begin
      S1 = ty_function:domain(Function),
      S2 = ty_function:codomain(Function),
      (ty_rec:is_subtype(T1, S1) orelse ty_rec:is_subtype(ty_function:codomains_intersect(P), ty_rec:negate(T2)) )
        andalso
        phi_v3(T1, ty_rec:intersect(T2, S2), P)
        andalso
        phi_v3(ty_rec:diff(T1, S1), T2, P)
    end.

prop_phi_invariant1() ->
  ?FORALL(
    {T1, T2, P, D, C},
    {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()}), limited_ast(), limited_ast()},
    begin
      PFuns = lists:map(fun({D, C}) -> ty_function:function(D, C) end, lists:sublist(P, 4)),
      phi_v0(T1, T2, PFuns, D, C) =:= phi_v1(ty_rec:diff(T1, D), ty_rec:diff(C, T2), PFuns)
    end
  ).

% invariant used for optimizing phi_v1 -> phi_v2b
% can be proved with induction over P
prop_phi_invariant2() ->
  ?FORALL({T, P}, {limited_ast(), list({limited_ast(), limited_ast()})},
    begin
      PFuns = lists:map(fun({D, C}) -> ty_function:function(D, C) end, lists:sublist(P, 5)),
      true = phi_v1(ty_rec:empty(), T, PFuns),
      true = phi_v1(T, ty_rec:empty(), PFuns),
      true
    end
  ).

prop_phi_equivalence() ->
  ?FORALL(
    {T1, T2, P},
    {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()})},
    begin
      PFuns = lists:map(fun({D, C}) -> ty_function:function(D, C) end, lists:sublist(P, 4)),

      R1 = phi_v0(T1, T2, PFuns),
      R2 = phi_v1(T1, ty_rec:negate(T2), PFuns),
      R3 = phi_v2a(T1, ty_rec:negate(T2), PFuns),
      R4 = phi_v2b(T1, ty_rec:negate(T2), PFuns),
      R5 = phi_v3(T1, ty_rec:negate(T2), PFuns),

      R1 =:= R2 andalso
        R1 =:= R3 andalso
        R1 =:= R4 andalso
        R1 =:= R5

    end
  ).

% phi should terminate in reasonable amount of time
prop_phi_no_timeout() ->
  ?FORALL({T1, T2, P}, {limited_ast(), limited_ast(), list({limited_ast(), limited_ast()})},
    begin
      PFuns = lists:map(fun({D, C}) -> ty_function:function(D, C) end, P),
      phi_v2b(T1, ty_rec:negate(T2), PFuns),
%%      {Ti1, R} = timer:tc(fun() -> phi_v2(T1, T2, PFuns) end),
%%      io:format(user, "Res: ~p~n", [Ti1]),
      true
    end
  ).
