-module(dnf_ty_map).

-define(ATOM, ty_map).
-define(LEAF, ty_bool).
-define(NODE, ty_node).
-define(F(Z), fun() -> Z end).

-include("dnf/bdd.hrl").

is_empty_line({[], [], T}, ST) -> error(todo);
is_empty_line({[], Neg = [_ | _], T}, ST) ->
  % this is the special case on why we can't use is_empty_line of dnf_ty_tuple directly
  % the 'any' representation is different
  P1 = ty_node:make(dnf_ty_variable:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any()))),
  P2 = ty_node:make(dnf_ty_variable:functions(ty_functions:singleton(2, dnf_ty_function:any()))),
  PPos = ty_tuple:tuple([P1, P2]),
  is_empty_line({[PPos], Neg, T}, ST);
is_empty_line({Pos, Neg, _T}, ST) ->
  _T = ?LEAF:any(), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  dnf_ty_tuple:phi(ty_tuple:components(BigS), Neg, ST).

normalize_line({[], [], T}, Fixed, ST) -> error(todo);
normalize_line({[], Neg = [_ | _], T}, Fixed, ST) ->
  P1 = ty_rec:tuple(2, dnf_var_ty_tuple:any()),
  P2 = ty_rec:function(2, dnf_var_ty_function:any()),
  PPos = ty_tuple:tuple([P1, P2]),
  normalize_line({[PPos], Neg, T}, Fixed, ST);
normalize_line({Pos, Neg, _T}, Fixed, ST) ->
  _T = ?LEAF:any(), % sanity
  BigS = ty_tuple:big_intersect(Pos),
  dnf_ty_tuple:phi_norm(ty_tuple:components(BigS), Neg, Fixed, ST).

