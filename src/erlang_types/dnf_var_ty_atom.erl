-module(dnf_var_ty_atom).

-define(P, {ty_atom, ty_variable}).
-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_atom).

-export([apply_to_node/3]).
-export([is_empty/1, normalize/3, substitute/4]).
-export([var/1, ty_atom/1, all_variables/1]).
-export([to_singletons/1, transform/2]).

-include("bdd_var.hrl").

ty_atom(Atom) -> terminal(Atom).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, T) -> ty_atom:is_empty(T).

normalize(Ty, Fixed, M) -> dnf(Ty, {
  fun(Pos, Neg, Atom) -> ty_atom:normalize(Atom, Pos, Neg, Fixed, M) end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun([], [], T) -> ty_atom:to_singletons(T); (_, _, _) -> [] end,
  fun erlang:'++'/2
  }).