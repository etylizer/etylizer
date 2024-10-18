-module(dnf_var_ty_function).

-define(ELEMENT, ty_variable).
-define(TERMINAL, dnf_ty_function).
-define(F(Z), fun() -> Z end).


-export([is_empty_corec/2]).
-export([normalize_corec/4, substitute/4]).
-export([var/1, function/1]).

-include("dnf/bdd_var.hrl").

function(Tuple) -> terminal(Tuple).
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
    true -> io:format(user,"~p vs ~p (~p)~n",[Time, Time2, Time/Time2]);
    _ -> ok
  end,
  Sol.
  

% substitution delegates to dnf_ty_tuple substitution
apply_to_node(Node, Map, Memo) ->
  dnf_ty_function:substitute(Node, Map, Memo, fun(N, Subst, M) -> ty_function:substitute(N, Subst, M) end).


simplify([]) -> [];
simplify(Dnf) ->
  DnfFun = lists:flatten([[{PosVar, NegVar, Pos, Neg} || {Pos, Neg, 1} <- ?TERMINAL:get_dnf(DnfFuns)] || {PosVar, NegVar, DnfFuns} <- Dnf]),

  % Check if any summand is 0
  begin
    lists:foreach(fun
      ({_, _, [], []}) -> ok;
      ({Pvar, Nvar, Pos, Neg}) -> 
        Ty = ty_rec:of_function_dnf(Pvar, Nvar, Pos, Neg),
        case ty_rec:is_empty(Ty) of true -> error(todo); _ -> ok end,
        ok
    end, DnfFun)
  end,

  %[check_useless(F) || ],
  Dnf.