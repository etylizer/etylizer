-module(dnf_var_ty_function).

-define(P, {dnf_ty_function, ty_variable}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2, is_empty/1]).

%%
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_any/1, normalize/4, substitute/4]).

-export([var/1, function/1, all_variables/1, has_ref/2, transform/2]).

-type dnf_function() :: term().
-type ty_function() :: dnf_function(). % ty_function:type()
-type variable() :: term(). % variable:type()
-type dnf_var_function() :: term().

-spec function(ty_function()) -> dnf_var_function().
function(Tuple) -> gen_bdd:terminal(?P, Tuple).

-spec var(variable()) -> dnf_var_function().
var(Var) -> gen_bdd:element(?P, Var).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

is_any(B) -> gen_bdd:is_any(?P, B).
is_empty(TyBDD) -> gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).
is_empty_coclause(_Pos, _Neg, T) -> dnf_ty_function:is_empty(T).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

normalize(Size, Ty, Fixed, M) -> normalize(Size, Ty, [], [], Fixed, M).

normalize(_, {terminal, 0}, _, _, _, _) -> [[]]; % satisfiable
normalize(Size, {terminal, Function}, PVar, NVar, Fixed, M) ->
  case ty_ref:is_normalized_memoized(Function, Fixed, M) of
    true ->
      % TODO test case
      error({todo, extract_test_case, memoize_function}); %[[]];
    miss ->
      % memoize only non-variable component t0
      dnf_ty_function:normalize(Size, Function, PVar, NVar, Fixed, sets:union(M, sets:from_list([Function])))
  end;
normalize(Size, {node, Variable, PositiveEdge, NegativeEdge}, PVar, NVar, Fixed, M) ->
  constraint_set:meet(
    ?F(normalize(Size, PositiveEdge, [Variable | PVar], NVar, Fixed, M)),
    ?F(normalize(Size, NegativeEdge, PVar, [Variable | NVar], Fixed, M))
  ).

substitute(MkTy, T, M, Memo) -> gen_bdd:substitute(?P, MkTy, T, M, Memo).

has_ref(Ty, Ref) -> gen_bdd:has_ref(?P, Ty, Ref).

all_variables({Default, Others}) when is_map(Others) ->
  all_variables(Default) ++ lists:map(fun({_K,V}) -> all_variables(V) end, maps:to_list(Others));
all_variables({terminal, 0}) -> [];
all_variables({terminal, Tuple}) -> dnf_ty_function:all_variables(Tuple);
all_variables({node, Variable, PositiveEdge, NegativeEdge}) ->
[Variable] ++ all_variables(PositiveEdge) ++ all_variables(NegativeEdge).

transform({terminal, 0}, #{empty := E}) -> E();
transform({terminal, Fun}, Ops) ->
  dnf_ty_function:transform(Fun, Ops);
transform({node, Variable, PositiveEdge, NegativeEdge},
    Ops = #{negate := Negate, var := ToVar, union := Union, intersect := Intersect}) ->
  AstVar = ToVar(Variable),
  Union([
    Intersect([AstVar, transform(PositiveEdge, Ops)]),
    Intersect([Negate(AstVar), transform(NegativeEdge, Ops)])
  ]).

%%-ifdef(TEST).
%%-include_lib("eunit/include/eunit.hrl").
%%
%%usage_test() ->
%%  %   any arrow
%%  TIa = ty_rec:empty(),
%%  TIb = ty_rec:empty(),
%%  Ty_F1 = ty_rec:function(dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(TIa, TIb)))),
%%
%%  %   any arrow 2
%%  Ty_F2 = ty_rec:function(),
%%
%%  true = ty_rec:is_subtype(Ty_F1, Ty_F2),
%%  true = ty_rec:is_subtype(Ty_F2, Ty_F1),
%%%%  io:format(user, "~p~n", [Bdd]),
%%
%%  ok.
%%
%%-endif.
