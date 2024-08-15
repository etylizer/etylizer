-module(dnf_ty_map).

-define(ELEMENT, ty_map).
-define(TERMINAL, bdd_bool).
-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/5, substitute/4, apply_to_node/3]).
-export([map/1, all_variables/1, transform/2]).

-include("bdd_node.hrl").

map(TyMap) -> node(TyMap).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> true;
    _ -> phi(ty_map:big_intersect(Pos), Neg)
  end.

phi(_, []) -> false;
phi(P, [N | Ns]) ->
  {Ls, St, Y1, Y2} = ty_map:comprehend_diff(P, N),
  case ty_rec:is_empty(Y1) andalso ty_rec:is_empty(Y2) andalso lists:all(fun ty_map:field_empty/1, maps:values(St)) of
    true ->
      FilteredLs = [X || {_, Fld} = X <- maps:to_list(Ls), not ty_map:field_empty(Fld)],
      ToCheck = [ty_map:anymap(#{L => Fld}) || {L, Fld} <- FilteredLs],
      lists:all(fun(M) -> phi(ty_map:intersect(P, M), Ns) end, ToCheck);
    false ->
      phi(P, Ns)
  end.


normalize(TyMap, [], [], Fixed, M) ->
  % nmap rule
  dnf(TyMap, {normalize_coclause(Fixed, M), fun constraint_set:meet/2});
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).

normalize_coclause(Fixed, M) -> fun(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ -> phi_norm(ty_map:big_intersect(Pos), Neg, Fixed, M)
  end
                                end.

phi_norm(_, [], _, _) -> [];
phi_norm(P, [N | Ns], Fixed, M) ->
  {Ls, St, Y1, Y2} = ty_map:comprehend_diff(P, N),
  NormY  = [?F(ty_rec:normalize(Y1, Fixed, M)), ?F(ty_rec:normalize(Y2, Fixed, M))],
  NormSt = [?F(ty_map:field_normalize(Fld, Fixed, M)) || {{_, _}, Fld} <- maps:to_list(St)],
  NormLs = [?F(
    constraint_set:join(
      ?F(ty_map:field_normalize(Fld, Fixed, M)),
      ?F(phi_norm(ty_map:intersect(P, ty_map:anymap(#{L => Fld})), Ns, Fixed, M)))) || {L, Fld} <- maps:to_list(Ls)],

  constraint_set:join(
    ?F(meet_all(NormY ++ NormSt ++ NormLs)),
    ?F(phi_norm(P, Ns, Fixed, M))
  ).

meet_all(Cs) ->
  lists:foldr(fun(C, Rest) -> constraint_set:meet(C, ?F(Rest)) end, [[]], Cs).

apply_to_node(Node, SubstituteMap, Memo) ->
  substitute(Node, SubstituteMap, Memo, fun(N, S, M) -> ty_map:substitute(N, S, M) end).