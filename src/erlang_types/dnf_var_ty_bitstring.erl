-module(dnf_var_ty_bitstring).

-define(ELEMENT, ty_variable).
-define(TERMINAL, ty_bool).

-export([apply_to_node/3]).
-export([is_empty/1, normalize_corec/3, substitute/4]).
-export([var/1, bitstring/1, ty_bitstring/0, all_variables/2]).
-export([transform/2]).

-include("bdd_var.hrl").

ty_bitstring() -> terminal(?TERMINAL:any()).
bitstring(Terminal) -> terminal(Terminal).
var(Var) -> node(Var).

% partially generic
is_empty(TyBDD) -> dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

is_empty_coclause(_Pos, _Neg, T) -> ?TERMINAL:is_empty(T).

normalize_corec(Ty, Fixed, M) -> dnf(Ty, {
  fun(PVar, NVar, Bit) -> 
    case ty_bool:empty() of
      Bit -> [[]]; % empty: satisfiable
      _ ->
        case {PVar, NVar} of
          {[], []} -> []; % non-empty
          _ ->
            TyB = ty_rec:bitstring(),
            % ntlv rule
            ty_variable:normalize_corec(TyB, PVar, NVar, Fixed, fun(Var) -> ty_rec:bitstring(dnf_var_ty_bitstring:var(Var)) end, M)
          end
      end
    end,
  fun constraint_set:meet/2
}).

% not recursive, no op substitution
apply_to_node(Node, _StdMap, _Memo) ->
  Node.