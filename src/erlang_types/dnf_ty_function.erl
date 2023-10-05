-module(dnf_ty_function).

-ifdef(TEST).
-export([explore_function_norm/6]).
-endif.

-define(P, {bdd_bool, ty_function}).
-define(F(Z), fun() -> Z end).


-export([equal/2, compare/2]).

%%
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([eval/1, is_empty/2, is_any/1, normalize/6, substitute/3]).

-export([function/1, all_variables/1, has_ref/2, transform/2]).

-type ty_ref() :: {ty_ref, integer()}.
-type dnf_function() :: term().
-type ty_function() :: dnf_function(). % ty_function:type()
-type dnf_ty_function() :: term().

-spec function(ty_function()) -> dnf_ty_function().
function(TyFunction) -> gen_bdd:element(?P, TyFunction).

% ==
% type interface
% ==
empty() -> gen_bdd:empty(?P).
any() ->
  gen_bdd:any(?P).

union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).

eval(B) -> gen_bdd:eval(?P, B).
is_any(B) -> gen_bdd:is_any(?P, B).

% ==
% basic interface
% ==

equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

is_empty(default, 0) -> true;
is_empty(default, {terminal, 1}) -> false;
is_empty(Size, TyDnf) ->
  is_empty(
    TyDnf,
    domains_to_tuple([ty_rec:empty() || _ <- lists:seq(1, Size)]), [], []
  ).

is_empty(0, _, _, _) -> true;
% TODO should only be {terminal, 1}, not just 1!
%%is_empty(1, _, _, []) -> false;
is_empty({terminal, 1}, _, _, []) -> false;
is_empty({terminal, 1}, BigSTuple, P, [Function | N]) ->
  Ts = ty_function:domains(Function),
  T2 = ty_function:codomain(Function),
  (
  %% ∃ Ts-->T2 ∈ N s.t.
  %%    Ts is in the domains of the function
  %%    BigS is the union of all domains of the positive function intersections
  ty_rec:is_subtype(domains_to_tuple(Ts), BigSTuple)
    andalso
    explore_function(domains_to_tuple(Ts), ty_rec:negate(T2), P)
  )
  %% Continue searching for another arrow ∈ N
    orelse
    is_empty({terminal, 1}, BigSTuple, P, N)
  ;
is_empty({node, Function, L_BDD, R_BDD}, BigS, P, N) ->
  Ts = ty_function:domains(Function),
  is_empty(L_BDD, ty_rec:union(BigS, domains_to_tuple(Ts)), [Function | P], N)
  andalso
    is_empty(R_BDD, BigS, P, [Function | N])
.

domains_to_tuple(Domains) ->
  ty_rec:tuple(length(Domains), dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(Domains)))).

% optimized phi' (4.10) from paper covariance and contravariance
% justification for this version of phi can be found in `prop_phi_function.erl`
-spec explore_function(ty_ref(), ty_ref(), [term()]) -> boolean().
explore_function(Ts, T2, []) ->
  ty_rec:is_empty(T2) orelse ty_rec:is_empty(Ts);
explore_function(Ts, T2, [Function | P]) ->
  ty_rec:is_empty(Ts) orelse ty_rec:is_empty(T2)
  orelse
    begin
      BigS1 = domains_to_tuple(ty_function:domains(Function)),
      S2 = ty_function:codomain(Function),
      explore_function(Ts, ty_rec:intersect(T2, S2), P)
        andalso
        explore_function(ty_rec:diff(Ts, BigS1), T2, P)
    end.

normalize({default, _}, 0, [], [], _, _) -> [[]];
normalize({default, _}, {terminal, 1}, [], [], _, _) -> [];
normalize(Size, TyFunction, [], [], Fixed, M) ->
  % cduce arrow rule
  normalize_cduce({Size, TyFunction}, Fixed, M, {[], []});
normalize(Size, DnfTyFunction, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:function(Size, dnf_var_ty_function:function(DnfTyFunction)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:function(Size, dnf_var_ty_function:var(Var)) end, M).

normalize_cduce({_, 0}, _, _, _) -> [[]]; % empty
normalize_cduce({Size, {terminal, 1}}, Fixed, M, PN) -> norm_arrow(Size, Fixed, M, PN); % non-empty
normalize_cduce({Size, {node, Function, L_BDD, R_BDD}}, Fixed, M, {P, N}) ->
  constraint_set:meet(
    ?F(normalize_cduce({Size, L_BDD}, Fixed, M, {[Function | P], N})),
    ?F(normalize_cduce({Size, R_BDD}, Fixed, M, {P, [Function | N]}))
  ).


norm_arrow(Size, Delta, Mem, {LPos, []}) -> [];
norm_arrow(Size, Delta, Mem, {LPos, [Fneg | N]}) ->
  T1 = domains_to_tuple(ty_function:domains(Fneg)),
  T2 = ty_function:codomain(Fneg),
  Con1 = ?F(ty_rec:normalize(T1, Delta, Mem)),
  Con2 = ?F(aux_arrow(Size, Delta, Mem, T1, ty_rec:negate(T2), LPos)),
  Con0 = ?F(norm_arrow(Size, Delta, Mem, {LPos, N})),
  D1 = ?F(constraint_set:join(Con1, Con2)),
  constraint_set:join(D1, Con0).


aux_arrow(Size, Delta, Mem, T1, Acc, []) -> [];
aux_arrow(Size, Delta, Mem, T1, Acc, [FP | P]) ->
  S1 = domains_to_tuple(ty_function:domains(FP)),
  S2 = ty_function:codomain(FP),

  T1S1 = ty_rec:diff(T1, S1),
  Acc1 = ty_rec:intersect(Acc, S2),

  Con1 = ?F(ty_rec:normalize(T1S1, Delta, Mem)),
  Con10 = ?F(aux_arrow(Size, Delta, Mem, T1S1, Acc, P)),
  Con11 = ?F(constraint_set:join(Con1, Con10)),

  Con2 = ?F(ty_rec:normalize(Acc1, Delta, Mem)),
  Con20 = ?F(aux_arrow(Size, Delta, Mem, T1, Acc1, P)),
  Con22 = ?F(constraint_set:join(Con2, Con20)),
  constraint_set:meet(Con11, Con22).



explore_function_norm(_Size, BigT1, T2, [], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize(BigT1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize(T2, Fixed, M)),
  constraint_set:join( NT1, NT2 );
explore_function_norm(Size, T1, T2, [Function | P], Fixed, M) ->
  NT1 = ?F(ty_rec:normalize(T1, Fixed, M)),
  NT2 = ?F(ty_rec:normalize(T2, Fixed, M)),

  S1 = domains_to_tuple(ty_function:domains(Function)),
  S2 = ty_function:codomain(Function),

  NS1 = ?F(explore_function_norm(Size, T1, ty_rec:intersect(T2, S2), P, Fixed, M)),
  NS2 = ?F(explore_function_norm(Size, ty_rec:diff(T1, S1), T2, P, Fixed, M)),

  constraint_set:join(NT1,
    ?F(constraint_set:join(NT2,
      ?F(constraint_set:meet(NS1, NS2))))).

substitute(0, _, _) -> 0;
substitute({terminal, 1}, _, _) ->
  {terminal, 1};
substitute({node, TyFunction, L_BDD, R_BDD}, Map, Memo) ->
  S2 = ty_function:codomain(TyFunction),

  NewDomains = lists:map(fun(E) -> ty_rec:substitute(E, Map, Memo) end, ty_function:domains(TyFunction)),
  NewS2 = ty_rec:substitute(S2, Map, Memo),

  NewTyFunction = ty_function:function(NewDomains, NewS2),

  union(
    intersect(function(NewTyFunction), substitute(L_BDD, Map, Memo)),
    intersect(negate(function(NewTyFunction)), substitute(R_BDD, Map, Memo))
  ).

has_ref(0, _) -> false;
has_ref({terminal, _}, _) -> false;
has_ref({node, Function, PositiveEdge, NegativeEdge}, Ref) ->
  ty_function:has_ref(Function, Ref)
  orelse
  has_ref(PositiveEdge, Ref)
    orelse
    has_ref(NegativeEdge, Ref).

all_variables(0) -> [];
all_variables({terminal, _}) -> [];
all_variables({node, Function, PositiveEdge, NegativeEdge}) ->
  ty_rec:all_variables(domains_to_tuple(ty_function:domains(Function)))
    ++ ty_rec:all_variables(ty_function:codomain(Function))
    ++ all_variables(PositiveEdge)
    ++ all_variables(NegativeEdge).


transform(0, #{empty := F}) -> F();
transform({terminal, 1}, #{any_fun := F}) -> F();
transform({node, Function, PositiveEdge, NegativeEdge}, Ops = #{negate := N, union := U, intersect := I} ) ->
  NF = ty_function:transform(Function, Ops),

  U([
    I([NF, transform(PositiveEdge, Ops)]),
    I([N(NF), transform(NegativeEdge, Ops)])
  ]).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

%%normalize2_test_() ->
%%  {timeout, 3000,
%%    fun() ->
%%      %   norm(b, ~b ^ N, []) == { {(b <= 0)} {(N <= b)} }
%%      Alpha = ty_variable:new("Alpha"),
%%      Beta = ty_variable:new("Beta"), TyBeta = ty_rec:variable(Beta),
%%      N = ty_rec:atom(),
%%
%%      T1 = TyBeta,
%%      T2 = ty_rec:intersect(ty_rec:negate(TyBeta), N),
%%      Res = explore_function_norm(T1, T2, [], sets:new()),
%%
%%      io:format(user, "Done ~p~n", [Res]),
%%
%%      % TODO check via equivalence instead of syntactically
%%      Res = [[{Beta, ty_rec:empty(), ty_rec:empty()}], [{Beta, N, ty_rec:any()}]],
%%
%%      ok
%%    end
%%  }.
-endif.
