-module(dnf_ty_map).

-define(ELEMENT, ty_map).
-define(TERMINAL, bdd_bool).
-define(NORM_TUP, fun dnf_ty_tuple:normalize/6).
-define(NORM_FUN, fun dnf_ty_function:normalize/6).
-define(F(Z), fun() -> Z end).

-export([is_empty/1, normalize/5, substitute/4, apply_to_node/3]).
-export([map/1, all_variables/1, transform/2]).

-include("bdd_node.hrl").

map(TyMap) -> node(TyMap).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(Pos, Neg, T) ->
  case {Pos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    _ ->
      BigInt = lists:foldr(fun ty_map:intersect/2, ty_map:any(), Pos),
      phi(BigInt, Neg)
  end.

phi({ty_map, Tup, Fun}, []) ->
  dnf_ty_tuple:is_empty(Tup)
    andalso Fun /= dnf_ty_function:any();

phi(P = {ty_map, Pt, Pf}, [{ty_map, Nt, Nf} | Ns]) ->
  DiffTup = dnf_ty_tuple:diff(Pt, Nt),
  DiffFun = dnf_ty_function:diff(Pf, Nf),
  (dnf_ty_tuple:is_empty(DiffTup)
    andalso dnf_ty_function:is_empty(DiffFun)) orelse phi(P, Ns).


normalize(TyMap, [], [], Fixed, M) ->
  % nmap-unrestricted rule
  dnf(TyMap, {normalize_coclause(Fixed, M), fun constraint_set:meet/2});
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).

normalize_coclause(Fixed, M) -> fun(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ ->
      BigInt = lists:foldr(fun ty_map:intersect/2, ty_map:any(), Pos),
      phi_norm(BigInt, Neg, Fixed, M)
  end
                                end.

phi_norm({ty_map, Pt, Pf}, [], Fixed, M) ->
  constraint_set:meet(
    ?F(?NORM_TUP(2, Pt, [], [], Fixed, M)),
    ?F(?NORM_FUN(1, Pf, [], [], Fixed, M))
  );
phi_norm(P = {ty_map, Pt, Pf}, [{ty_map, Nt, Nf} | Ns], Fixed, M) ->
  DiffTup = dnf_ty_tuple:diff(Pt, Nt),
  DiffFun = dnf_ty_function:diff(Pf, Nf),
  X = constraint_set:join(
    ?F(constraint_set:meet(
      ?F(?NORM_TUP(2, DiffTup, [], [], Fixed, M)),
      ?F(?NORM_FUN(2, DiffFun, [], [], Fixed, M))
    )),
    ?F(phi_norm(P, Ns, Fixed, M))
  ),
  X.

apply_to_node(Node, Map, Memo) ->
  substitute(Node, Map, Memo, fun(N, S, M) -> ty_map:substitute(N, S, M) end).
