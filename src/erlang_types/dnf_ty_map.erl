-module(dnf_ty_map).

-define(P, {bdd_bool, ty_map}).
-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(NORM, fun ty_rec:normalize/3).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/5, substitute/4]).
-export([map/1, all_variables/1, has_ref/2, transform/2]).

% fully generic
map(TyMap) -> gen_bdd:element(?P, TyMap).
empty() -> gen_bdd:empty(?P).
any() -> gen_bdd:any(?P).
substitute(MkTy, TyBDD, Map, Memo) -> gen_bdd:substitute(?P, MkTy, TyBDD, Map, Memo).
union(B1, B2) -> gen_bdd:union(?P, B1, B2).
intersect(B1, B2) -> gen_bdd:intersect(?P, B1, B2).
diff(B1, B2) -> gen_bdd:diff(?P, B1, B2).
negate(B1) -> gen_bdd:negate(?P, B1).
is_any(B) -> gen_bdd:is_any(?P, B).
has_ref(TyBDD, Ref) -> gen_bdd:has_ref(?P, TyBDD, Ref).
all_variables(TyBDD) -> gen_bdd:all_variables(?P, TyBDD).
transform(TyBDD, OpMap) -> gen_bdd:transform(?P, TyBDD, OpMap).
equal(B1, B2) -> gen_bdd:equal(?P, B1, B2).
compare(B1, B2) -> gen_bdd:compare(?P, B1, B2).

% partially generic
is_empty(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {fun is_empty_coclause/3, fun gen_bdd:is_empty_union/2}).

% module specific implementations
is_empty_coclause(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> true;
    _ -> phi(ty_map:big_intersect(Pos), Neg)
end.

phi(_, []) -> false;
phi(P, [N | Ns]) ->
  StepsDiff = ty_map:diff_k_steps(P, N),
  W1Diff = ty_map:diff_omega1_step(P, N),

  case lists:all(fun ty_rec:is_empty/1, [W1Diff | maps:values(StepsDiff)]) of
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
  gen_bdd:dnf(?P, TyMap, {normalize_coclause(Fixed, M), fun constraint_set:meet/2});
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
  StepsDiff = ty_map:diff_k_steps(P, N),
  W1Diff = ty_map:diff_omega1_step(P, N),
  LabelsDiff = ty_map:diff_labels(P, N),
  {O1, O2} = ty_map:omegas(P),
  {O11, O22} = ty_map:omegas(N),

  NormedKeyVars = ?F(norm_key_variables(O1, O11, O2, O22, ty_map:key_variables(P), ty_map:key_variables(N), Fixed, M)),

  ToNorm1 = [?F(?NORM(TyRef, Fixed, M)) || TyRef <- [W1Diff | maps:values(StepsDiff)]],
  ToNorm2 = [begin
               X = ?F(elim_assoc_conflict(?NORM(TyRef, Fixed, M), A)),
               Y = ?F(elim_assoc_conflict(phi_norm(ty_map:intersect(P, anymap(AL, TyRef)), Ns, Fixed, M), A)),
               ?F(constraint_set:join(X, Y))
             end || AL = {A, _} := TyRef <- LabelsDiff],

  constraint_set:join(
    ?F(meet_all([NormedKeyVars | ToNorm1 ++ ToNorm2])),
    ?F(phi_norm(P, Ns, Fixed, M))
  ).


norm_key_variables(O1, O11, O2, O22, KeyVarsInPos, KeyVarsInNeg, Fixed, M) ->
  Bound = fun(Var, Lower, Upper) -> constraint_set:meet(
    ?F(?NORM(ty_rec:diff(Lower, Var), Fixed, M)),
    ?F(?NORM(ty_rec:diff(Var, Upper), Fixed, M)))
           end,
  NormPos = [case A of
               ?MAN -> ?F(Bound(Var, ty_rec:diff(O1, O11), ty_rec:diff(O1, O11)));
               ?OPT -> ?F(Bound(Var, ty_rec:diff(O2, O22), ty_rec:diff(O2, O22)))
             end || {A, Var} <- KeyVarsInPos],
  NormNeg = [case A of
               ?MAN -> ?F(Bound(Var, ty_rec:diff(O11, O1), ty_rec:diff(O11, O1)));
               ?OPT -> ?F(Bound(Var, ty_rec:diff(O22, O2), O22))
             end || {A, Var} <- KeyVarsInNeg],

  meet_all(NormPos ++ NormNeg).


anymap(AL, TyRef) -> ty_map:map(#{AL => TyRef}, #{S => ty_rec:any() || S <- ty_map:step_names()}).
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