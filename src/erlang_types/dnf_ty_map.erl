-module(dnf_ty_map).

-define(ELEMENT, ty_map).
-define(TERMINAL, bdd_bool).

-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(NORM, fun ty_rec:normalize/3).

-export([is_empty/1, normalize/5, substitute/4, apply_to_node/3]).
-export([map/1, all_variables/2, transform/2]).

-include("bdd_node.hrl").

map(TyMap) -> node(TyMap).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause(Pos, Neg, T) ->
  case {Pos, Neg, bdd_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [_TNeg | _], _} ->
      P1 = ty_rec:tuple(2, dnf_var_ty_tuple:any()),
      P2 = ty_rec:function(2, dnf_var_ty_function:any()),
      PPos = ty_tuple:tuple([P1, P2]),
      BigS = ty_tuple:big_intersect([PPos]),
      dnf_ty_tuple:phi(ty_tuple:components(BigS), Neg);
    {Pos, Neg, _} ->
      BigS = ty_tuple:big_intersect(Pos),
      dnf_ty_tuple:phi(ty_tuple:components(BigS), Neg)
  end.

normalize(TyMap, [], [], Fixed, M) ->
  % nmap rule
  dnf(TyMap, {
    fun
      ([], [], T) ->
        case bdd_bool:empty() of T -> [[]]; _ -> [] end;
      ([], Neg = [_TNeg | _], T) ->
        case bdd_bool:empty() of 
          T -> [[]]; 
          _ -> 
            P1 = ty_rec:tuple(2, dnf_var_ty_tuple:any()),
            P2 = ty_rec:function(2, dnf_var_ty_function:any()),
            PPos = ty_tuple:tuple([P1, P2]),
            BigS = ty_tuple:big_intersect([PPos]),
            dnf_ty_tuple:phi_norm(2, ty_tuple:components(BigS), Neg, Fixed, M)
        end;
      (Pos, Neg, T) ->
        case bdd_bool:empty() of
          T -> [[]];
          _ ->
            BigS = ty_tuple:big_intersect(Pos),
            dnf_ty_tuple:phi_norm(2, ty_tuple:components(BigS), Neg, Fixed, M)
        end
    end,
    fun constraint_set:meet/2});
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).


apply_to_node(Node, SubstituteMap, Memo) ->
  substitute(Node, SubstituteMap, Memo, fun(N, S, M) -> ty_map:substitute(N, S, M) end).