-module(dnf_var_ty_ref).

-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_rec).
% see comment in bdd.hrl
-define(TRANSFORM, true).

-export([is_empty/1,normalize/3, substitute/4]).
-export([var/1, ref/1, all_variables/1, transform/2, apply_to_node/3]).

-include("bdd_var.hrl").

% fully generic
ref(Ty) -> terminal(Ty).
var(Var) -> node(Var).

% partially generic
is_empty_coclause(_Pos, _Neg, {ty_ref, 0}) -> false;
is_empty_coclause(_Pos, _Neg, {ty_ref, 1}) -> true;
is_empty_coclause(_Pos, _Neg, T) -> ty_rec:is_empty(T).
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).
normalize(Ty, Fixed, M) -> 
  dnf(Ty, {
    fun(Pos, Neg, DnfTy) -> normalize_coclause(Pos, Neg, DnfTy, Fixed, M) end,
    fun constraint_set:meet/2
  }).

% module specific implementations
normalize_coclause([], [], Ty, Fixed, M) ->
  ty_rec:normalize(Ty, Fixed, M);
normalize_coclause(PVar, NVar, DnfTy, Fixed, M) ->
  Ty = ty_rec:tuple(1, dnf_var_ty_ref:ref(DnfTy)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:tuple(1, dnf_var_ty_ref:var(Var)) end, M).


% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  ty_rec:substitute(Node, Map, Memo).


% see comment in bdd.hrl
transform(Ty, Ops = #{to_tuple := Tuple, negate := Negate, intersect := Intersect, union := Union}) ->
  dnf(Ty, {
    fun
      (P,N,T) ->
        P1 = Tuple([T]),
        P2 = [?ELEMENT:transform(V, Ops) || V <- P],
        P3 = [Negate(?ELEMENT:transform(V, Ops)) || V <- N],
        Intersect([P1] ++ P2 ++ P3)
    end,
    fun(F1, F2) -> Union([F1(), F2()]) end
  }).