-module(dnf_ty_map).

-define(ELEMENT, ty_map).
-define(TERMINAL, ty_bool).

-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).

-export([is_empty_corec/2, normalize_corec/5, substitute/4, apply_to_node/3]).
-export([map/1, all_variables/2, transform/2]).

-include("bdd_node.hrl").

map(TyMap) -> node(TyMap).

is_empty_corec(TyBDD, M) ->
  dnf(TyBDD, {fun(P, N, T) -> is_empty_coclause_corec(P, N, T, M) end, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause_corec(Pos, Neg, T, M) ->
  case {Pos, Neg, ty_bool:empty()} of
    {_, _, T} -> true;
    {[], [], _} -> false;
    {[], [_TNeg | _], _} ->
      P1 = ty_rec:tuple(2, dnf_var_ty_tuple:any()),
      P2 = ty_rec:function(2, dnf_var_ty_function:any()),
      PPos = ty_tuple:tuple([P1, P2]),
      BigS = ty_tuple:big_intersect([PPos]),
      dnf_ty_tuple:phi_corec(ty_tuple:components(BigS), Neg, M);
    {Pos, Neg, _} ->
      BigS = ty_tuple:big_intersect(Pos),
      dnf_ty_tuple:phi_corec(ty_tuple:components(BigS), Neg, M)
  end.

normalize_corec(TyMap, [], [], Fixed, M) ->
  % nmap rule
  dnf(TyMap, {
    fun
      ([], [], T) ->
        case ty_bool:empty() of T -> [[]]; _ -> [] end;
      ([], Neg = [_TNeg | _], T) ->
        case ty_bool:empty() of 
          T -> [[]]; 
          _ -> 
            P1 = ty_rec:tuple(2, dnf_var_ty_tuple:any()),
            P2 = ty_rec:function(2, dnf_var_ty_function:any()),
            PPos = ty_tuple:tuple([P1, P2]),
            BigS = ty_tuple:big_intersect([PPos]),
            dnf_ty_tuple:phi_norm_corec(2, ty_tuple:components(BigS), Neg, Fixed, M)
        end;
      (Pos, Neg, T) ->
        case ty_bool:empty() of
          T -> [[]];
          _ ->
            BigS = ty_tuple:big_intersect(Pos),
            dnf_ty_tuple:phi_norm_corec(2, ty_tuple:components(BigS), Neg, Fixed, M)
        end
    end,
    fun constraint_set:meet/2});
normalize_corec(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize_corec(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).


apply_to_node(Node, SubstituteMap, Memo) ->
  substitute(Node, SubstituteMap, Memo, fun(N, S, M) -> ty_map:substitute(N, S, M) end).