-module(dnf_var_ty_bool).

-define(ELEMENT, ty_variable).
-define(TERMINAL, bdd_bool).

-export([is_empty/1,normalize/3, substitute/4]).
-export([var/1, bool/1, all_variables/1, transform/2, apply_to_node/3]).

-include("bdd_var.hrl").

% fully generic
bool(Ty) -> terminal(Ty).
var(Var) -> node(Var).

% partially generic
is_empty_coclause(_Pos, _Neg, T) -> bdd_bool:is_empty(T).
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
normalize(Ty, Fixed, M) -> 
  dnf(Ty, {
    fun(Pos, Neg, DnfTy) -> normalize(DnfTy, Pos, Neg, Fixed, M) end,
    fun constraint_set:meet/2
  }).

normalize(Bool, [], [], _Fixed, _) ->
  % Fig. 3 Line 3
  case ?TERMINAL:is_empty(Bool) of
    true -> [[]];
    false -> []
  end;
normalize(0, _, _, _, _) -> [[]];
normalize(Bool, PVar, NVar, Fixed, M) ->
  % TODO dnf_var_ty_bool should not know that it is a 0-tuple, hack
  Ty = ty_rec:tuple(0, dnf_var_ty_bool:bool(Bool)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(0, dnf_var_ty_bool:var(Var)) end, M).


% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, _Map, _Memo) ->
  Node.
