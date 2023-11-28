-module(dnf_ty_map).

-define(P, {bdd_bool, ty_map}).
-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).

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
    _ ->
      BigIntersect = lists:foldr(fun ty_map:b_intersect/2, ty_map:b_anymap(), Pos),
      phi(BigIntersect, Neg)
  end.

phi(P, []) ->
  {ty_map, Labels, Steps} = P,
  #{} == filter_empty_labels(Labels) andalso #{} == Steps;
phi(P, [N]) ->
  {ty_map, LsDiff, StDiff} = ty_map:b_diff(P, N),
  NoEmpties = maps:filter(fun(_, TyRef) -> not ty_rec:is_empty(TyRef) end, StDiff),
  phi(ty_map:map(LsDiff, NoEmpties), []);
phi(P, [N | Ns]) ->
  {ty_map, Labels, Steps} = P,
  % ∀ ℓ ∈ L . P(ℓ) \ N(ℓ)
  % ∀ 𝑘 ∈ Steps . (def(P))𝑘 \ (def(N))𝑘
  {ty_map, LsDiff, StDiff} = ty_map:b_diff(P, N),
  % ∀ 𝑘 . (def(P))𝑘 \ (def(N))𝑘 ~ 0
  case lists:all(fun ty_rec:is_empty/1, maps:values(StDiff)) of
    true ->
      % ∀ ℓ ∈ L . P(ℓ) \ N(ℓ) <> 0
      Rest = filter_empty_labels(LsDiff),
      % ∀ ℓ ∈ Rest . Φ(P ∧ {ℓ : ¬N(ℓ)}, Ns)
      lists:all(
        fun({AL, TyRef}) -> phi(ty_map:map(Labels#{AL => TyRef}, Steps), Ns) end,
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
    _ ->
      BigIntersect = lists:foldr(fun ty_map:b_intersect/2, ty_map:b_anymap(), Pos),
      phi_norm(BigIntersect, Neg, Fixed, M)
  end
                                end.

phi_norm({ty_map, Labels, Steps}, _, _, _) when Labels == #{}, Steps == #{} ->
  [[]];
phi_norm(P, Ns, Fixed, M) ->
  {ty_map, _, _} = P,
  KeyConstr = ?F(norm_key_variables(P, Fixed, M)),
  NsConstr = ?F(norm_ns(P, Ns, Fixed, M)),
  meet_all([KeyConstr, NsConstr]).

norm_ns(_, [], _, _) -> [];
norm_ns(P, [N | Ns], Fixed, M) ->
  constraint_set:join(?F(norm_n(P, N, Ns, Fixed, M)), ?F(norm_ns(P, Ns, Fixed, M))).

norm_n(P, N, Ns, Fixed, M) ->
  {ty_map, Labels, Steps} = P,
  % ∀ 𝑘 ∈ Steps . (def'(P))𝑘 \ (def'(N))𝑘
  StepConstr = ?F(norm_steps(P, N, Fixed, M)),
  % ∀ ℓ ∈ L . P(ℓ)' \ N(ℓ)'
  {_, LsDiff, _} = ty_map:b_diff(P, N),

  KeyConstr1 = ?F(norm_key_variables(N, Fixed, M)),
  KeyConstr2 = ?F(norm_key_variables(P, N, Fixed, M)),
  LabelConstrList = [begin
                       ValConstr = ?F(elim_assoc_conflict(ty_rec:normalize(TyRef, Fixed, M), A)),
                       RestConstr = ?F(elim_assoc_conflict(norm_ns(ty_map:map(Labels#{AL => TyRef}, Steps), Ns, Fixed, M), A)),
                       ?F(constraint_set:join(ValConstr, RestConstr))
                     end
    || AL = {A, _} := TyRef <- LsDiff],
  meet_all([KeyConstr1, KeyConstr2, StepConstr | LabelConstrList]).


norm_steps(TyMap1, TyMap2, Fixed, M) ->
  {_, Labels, Steps} = TyMap1,
  {_, NegLabels, NegSteps} = TyMap2,
  VarValues1 = [Ty || {A, {Tag, _}} := Ty <- Labels, optional == A, var_key == Tag],
  VarValues2 = [Ty || {A, {Tag, _}} := Ty <- NegLabels, optional == A, var_key == Tag],
  meet_all([begin
              #{S := T2} = NegSteps,
              T11 = u([T1 | VarValues1]),
              T22 = u([T2 | VarValues2]),
              case T22 == ty_rec:empty() of
                true -> ?F(ty_rec:normalize(T1, Fixed, M));
                false -> ?F(ty_rec:normalize(ty_rec:diff(T11, T22), Fixed, M))
              end
            end
    || S := T1 <- Steps]).


%% Set upper bound for key variables in Map
norm_key_variables(TyMap = {_, Labels, _}, Fixed, M) ->
  UndefinedKeys = ty_rec:diff(ty_map:key_domain(), ty_map:key_domain(TyMap, false)),
  meet_all([case A of
              optional ->
                Upper = ty_rec:diff(TyVar, UndefinedKeys),
                ?F(ty_rec:normalize(Upper, Fixed, M));
              mandatory ->
                LabelKeys = u([TyRef || {_, {T, TyRef}} := _ <- Labels, var_key =/= T]),
                Upper = ty_rec:diff(TyVar, ty_rec:negate(LabelKeys)),
                ?F(ty_rec:normalize(Upper, Fixed, M))
            end
    || {A, {Tag, TyVar}} := _ <- Labels, var_key == Tag]).


%% Set lower bound for key variables in Map1 with respect to Map2 and vice versa
norm_key_variables(TyMap1, TyMap2, Fixed, M) ->
  DefinedKeys1 = ty_map:key_domain(TyMap1, true),
  DefinedKeys2 = ty_map:key_domain(TyMap2, true),
  Constrain =
    fun({_, Labels1, _}, {_, Labels2, _}, Flag) ->
      meet_all([case A of
                  optional ->
                    Lower = case Flag of 1 -> ty_rec:diff(TyVar, DefinedKeys2); 2 -> ty_rec:diff(DefinedKeys1, TyVar) end,
                    ?F(ty_rec:normalize(Lower, Fixed, M));
                  mandatory ->
                    case [TyRef || {AA, {_, TyRef}} := _ <- Labels2, mandatory == AA] of
                      [] when Flag == 1 -> ?F([[]]); % case: no mandatory keys in neg map
                      % [] when Flag == 2 -> ?F([]); % case: no mandatory keys in pos map -- handled it below, by setting var to 0, thus var discarded by substitution
                      X ->
                        LabelKeys = u(X),
                        Lower = ty_rec:diff(LabelKeys, TyVar),
                        Upper = ty_rec:diff(TyVar, LabelKeys),
                        ?F(constraint_set:meet(?F(ty_rec:normalize(Lower, Fixed, M)), ?F(ty_rec:normalize(Upper, Fixed, M))))
                    end
                end
        || {A, {Tag, TyVar}} := _ <- Labels1, var_key == Tag])
    end,
  constraint_set:meet(?F(Constrain(TyMap1, TyMap2, 1)), ?F(Constrain(TyMap2, TyMap1, 2))).


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
u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
meet_all(Cs) -> lists:foldr(fun(C, Rest) -> constraint_set:meet(C, ?F(Rest)) end, [[]], Cs).
