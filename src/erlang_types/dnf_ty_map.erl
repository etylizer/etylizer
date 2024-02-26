-module(dnf_ty_map).

-define(ELEMENT, ty_map).
-define(TERMINAL, bdd_bool).

-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(NORM, fun ty_rec:normalize/3).

-export([is_empty/1, normalize/5, substitute/4, apply_to_node/3]).
-export([map/1, all_variables/1, transform/2]).

-include("bdd_node.hrl").

map(TyMap) -> node(TyMap).

is_empty(TyBDD) ->
  dnf(TyBDD, {fun is_empty_coclause/3, fun is_empty_union/2}).

% module specific implementations
is_empty_coclause(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> true;
    _ -> phi(ty_map:big_intersect(Pos), Neg)
end.

phi(_, []) -> false;
phi(P, [N | Ns]) ->
  StepsDiff = ty_map:diff_steps(P, N),
  % without w1: classic phi function for quasi-k-step functions
  % checking w1 not needed when type variables not present
  case lists:all(fun ty_rec:is_empty/1, maps:values(StepsDiff)) of
    true ->
      Rest = filter_empty_labels(ty_map:diff_labels(P, N)),
      lists:all(
        fun({AL, TyRef}) -> phi(ty_map:intersect(P, anymap(AL, TyRef)), Ns) end,
        maps:to_list(Rest)
      );
    false -> phi(P, Ns)
  end.


normalize(TyMap, [], [], Fixed, M) ->
  % nmap rule
  dnf(TyMap, {normalize_coclause(Fixed, M), fun constraint_set:meet/2});
normalize(DnfTyMap, PVar, NVar, Fixed, M) ->
  Ty = ty_rec:map(dnf_var_ty_map:map(DnfTyMap)),
  % ntlv rule
  ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:map(dnf_var_ty_map:var(Var)) end, M).

normalize_coclause(Fixed, M) -> fun(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> [[]];
    _ -> phi_norm(ty_map:big_intersect(Pos), Neg, Fixed, M)
  end
                                end.

phi_norm(_, [], _, _) -> [];
phi_norm(P, [N | Ns], Fixed, M) ->
  StepsDiff = ty_map:diff_steps(P, N),
  W1Diff = ty_map:diff_w1(P, N),
  LabelsDiff = ty_map:diff_labels(P, N),

  NormedKeyVars = ?F(norm_key_variables(
    ty_map:key_variable_suite(P), ty_map:key_variable_suite(N),
    Fixed,
    M
  )),
  NormedSteps = [?F(?NORM(TyRef, Fixed, M)) || TyRef <- [W1Diff | maps:values(StepsDiff)]],
  NormedLabels = [begin
                    X = ?F(elim_assoc_conflict(?NORM(TyRef, Fixed, M), A)),
                    Y = ?F(elim_assoc_conflict(phi_norm(ty_map:intersect(P, anymap(AL, TyRef)), Ns, Fixed, M), A)),
                    ?F(constraint_set:join(X, Y))
                  end || {AL = {A, _}, TyRef} <- maps:to_list(LabelsDiff)],

  constraint_set:join(
    ?F(meet_all([NormedKeyVars | NormedSteps ++ NormedLabels])),
    ?F(phi_norm(P, Ns, Fixed, M))
  ).


norm_key_variables({O1, O2, PosManU, PosOptU}, {O11, O22, NegManU, NegOptU}, Fixed, M) ->
  Bound = fun(VarUnion, Lower, Upper) -> constraint_set:meet(
    ?F(?NORM(ty_rec:diff(Lower, VarUnion), Fixed, M)),
    ?F(?NORM(ty_rec:diff(VarUnion, Upper), Fixed, M)))
          end,
  {PosO1, PosO2} = {ty_rec:diff(O1, O11), ty_rec:diff(O2, O22)},
  {NegO1, NegO2} = {ty_rec:diff(O11, O1), ty_rec:diff(O22, O2)},

  meet_all([
    ?F(Bound(PosManU, PosO1, PosO1)),
    ?F(Bound(PosOptU, PosO2, PosO2)),
    ?F(Bound(NegManU, NegO1, NegO1)),
    ?F(Bound(NegOptU, NegO2, NegO2))
  ]).


apply_to_node(Node, SubstituteMap, Memo) ->
  substitute(Node, SubstituteMap, Memo, fun(N, S, M) -> ty_map:substitute(N, S, M) end).


anymap(AL, TyRef) -> ty_map:map(#{AL => TyRef}, maps:from_keys(ty_map:step_names(), ty_rec:any())).
filter_empty_labels(Labels) -> maps:filter(
  fun({?OPT, _}, _) -> true;
     ({?MAN, _}, TyRef) -> not ty_rec:is_empty(TyRef)
  end, Labels).
elim_assoc_conflict(_Constraints = C, _Association = A) ->
  case {C, A} of
    {[[]], ?OPT} -> []; % [[]] must only occur with mandatory
    {[], ?OPT} -> [[]]; % ⊥ exists as solution
    _ -> C
  end.
meet_all(Cs) -> lists:foldr(fun(C, Rest) -> constraint_set:meet(C, ?F(Rest)) end, [[]], Cs).