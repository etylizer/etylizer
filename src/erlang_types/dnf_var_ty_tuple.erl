-module(dnf_var_ty_tuple).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_tuple).
-define(F(Z), fun() -> Z end).

-export([normalize_corec/4, substitute/4]).
-export([var/1, tuple/1, is_empty_corec/2, apply_to_node/3]).

% implementations provided by bdd_var.hrl
-include("dnf/bdd_var.hrl").

tuple(Tuple) -> terminal(Tuple).
var(Var) -> node(Var).

normalize(Size, Ty, Fixed, M) -> 
  {Time2, Sol2} = timer:tc(fun() -> 
    dnf(Ty, {
      fun(Pos, Neg, DnfTy) -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      fun constraint_set:meet/2
    })
  end),
  {Time, Sol} = timer:tc(fun() -> 
    Dnf = simplify(get_dnf(Ty)),
    lists:foldl(fun({Pos, Neg, DnfTy}, Acc) -> 
      OtherLazy = fun() -> normalize_coclause(Size, Pos, Neg, DnfTy, Fixed, M) end,
      constraint_set:meet(Acc, OtherLazy)
    end, [[]], Dnf)
  end),
  case Time > 1000 orelse Time2 > 1000 of
    % true -> io:format(user,"~p vs ~p (~p)~n",[Time, Time2, Time/Time2]);
    _ -> ok
  end,
  Sol.

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_tuple:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_tuple:substitute(N, Subst, M) end).

to_singletons(TyBDD) -> dnf(TyBDD, {
  fun(_Pos = [], _Neg = [], T) -> dnf_ty_tuple:to_singletons(T); (_, _, _) -> [] end,
  fun(F1, F2) -> F1() ++ F2() end
}).
simplify(Dnf) ->
  %DnfFun = [{Pos, Neg, Fun}],
  %[check_useless(F) || ],
  Dnf.