-module(dnf_ty_list).

-define(ATOM, ty_list).
-define(LEAF, ty_bool).
-define(NODE, ty_node).
-define(F(Z), fun() -> Z end).

-include("dnf/bdd.hrl").

is_empty_line(Line, ST) ->
  dnf_ty_tuple:is_empty_line(Line, ST).

normalize_line(Line, Fixed, ST) ->
  dnf_ty_tuple:normalize_line(Line, Fixed, ST).
