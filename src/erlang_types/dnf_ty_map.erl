-module(dnf_ty_map).

-define(P, {bdd_bool, ty_map}).
-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).

-export([equal/2, compare/2]).
-export([empty/0, any/0, union/2, intersect/2, diff/2, negate/1]).
-export([is_empty/1, is_any/1, normalize/5, substitute/4]).
-export([map/1, all_variables/1, has_ref/2, transform/2, to_unf/1]).

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
    _ -> case Pos of
           [] -> false;
           _ ->
             BigIntersect = lists:foldr(fun ty_map:b_intersect/2, ty_map:b_anymap(), Pos),
             phi(BigIntersect, Neg)
         end
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

to_unf(TyBDD) ->
  gen_bdd:dnf(?P, TyBDD, {fun to_unf_coclause/3, fun ty_unf_map:union/2}).

to_unf_coclause(Pos, Neg, T) ->
  case bdd_bool:empty() of
    T -> ty_unf_map:empty();
    _ -> case Pos of
           [] -> ty_unf_map:empty();
           _ ->
             BigUnfIntersect = lists:foldr(fun ty_unf_map:b_intersect/2, ty_unf_map:any(), [ty_unf_map:map(P) || P <- Pos]),
             lists:foldr(
               fun(N, P) -> ty_unf_map:b_diff(P, N) end,
               BigUnfIntersect,
               [ty_unf_map:map(N) || N <- Neg]
             )
         end
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

phi_norm(P, [], Fixed, M) ->
  {ty_map, Labels, Steps} = P,
  case Labels == #{} and Steps == #{} of
    true -> [[]]; % satisfied
    false ->
      KeyC = constrain_key_vars(P, Fixed, M),
      C1 = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- Steps],
      C2 = [?F(ty_rec:normalize(TyRef2, Fixed, M)) || _ := TyRef2 <- Labels],
      (lazy_meet([KeyC | C1 ++ C2]))()
  end;
phi_norm(P, [N | Ns], Fixed, M) ->
  {ty_map, Labels, Steps} = P,
  {ty_map, NegLabels, NegSteps} = N,
  KeyC1 = constrain_key_vars(N, Fixed, M),
  KeyC2 = constrain_key_vars(P, N, Fixed, M),

  % ∀ 𝑘 ∈ Steps . (def'(P))𝑘 \ (def'(N))𝑘
  StDiff = var_steps_diff(Labels, Steps, NegLabels, NegSteps),
  % ∀ ℓ ∈ L . P(ℓ)' \ N(ℓ)'
  {_, LsDiff, _} = ty_map:b_diff(P, N),

  StepConstraints  = [?F(ty_rec:normalize(TyRef, Fixed, M)) || _ := TyRef <- StDiff],
  LabelConstraints = [
    begin
      X = ?F(elim_lbl_conflict(ty_rec:normalize(TyRef, Fixed, M), A)),
      Y = ?F(elim_lbl_conflict(phi_norm(ty_map:map(Labels#{AL => TyRef}, Steps), Ns, Fixed, M), A)),
      ?F(constraint_set:join(X, Y))
    end
    || AL = {A, _} := TyRef <- LsDiff
  ],
  Constraints = lazy_meet([KeyC1, KeyC2 | StepConstraints ++ LabelConstraints]),
  constraint_set:join(Constraints, ?F(phi_norm(P, Ns, Fixed, M))).


var_steps_diff(Labels, Steps, NegLabels, NegSteps) ->
  Empty = ty_rec:empty(),
  VarValues1 = [Ty || {A, {Tag, _}} := Ty <- Labels, optional == A andalso var_key == Tag],
  VarValues2 = [Ty || {A, {Tag, _}} := Ty <- NegLabels, optional == A andalso var_key == Tag],
  #{S => begin
           #{S := T2} = NegSteps,
           T22 = u([T2 | VarValues2]),
           case T22 of
             _ when T22 == Empty -> T1;
             _ -> ty_rec:diff(u([T1 | VarValues1]), T22)
           end
         end
    || S := T1 <- Steps}.


%% Set upper bound for var labels in Map
constrain_key_vars(Map = {_, Labels, _}, Fixed, M) ->
  UndefinedKeys = ty_rec:diff(ty_map:key_domain(), ty_map:key_domain(Map, false)),
  lazy_meet(
    [case A of
       optional ->
         Upper = ty_rec:diff(TyVar, UndefinedKeys),
         ?F(ty_rec:normalize(Upper, Fixed, M));
       mandatory ->
         LabelKeys = u([TyRef || {_, {T, TyRef}} := _ <- Labels, var_key =/= T]),
         Upper = ty_rec:diff(TyVar, ty_rec:negate(LabelKeys)),
         ?F(ty_rec:normalize(Upper, Fixed, M))
     end
      || {A, {Tag, TyVar}} := _ <- Labels, var_key == Tag]
  ).


%% Set lower bound for var labels in Map1 with respect to Map2 and vice versa
constrain_key_vars(TyMap1, TyMap2, Fixed, M) ->
  DefinedKeys1 = ty_map:key_domain(TyMap1, true),
  DefinedKeys2 = ty_map:key_domain(TyMap2, true),
  Constrain = fun({_, Labels1, _}, {_, Labels2, _}, Flag) ->
    lazy_meet(
      [case A of
         optional ->
           Lower = case Flag of 1 -> ty_rec:diff(TyVar, DefinedKeys2); 2 -> ty_rec:diff(DefinedKeys1, TyVar) end,
           ?F(ty_rec:normalize(Lower, Fixed, M));
         mandatory ->
           case [TyRef || {AA, {_, TyRef}} := _ <- Labels2, mandatory == AA] of
             [] when Flag == 1 -> ?F([[]]); % case: no mandatory keys in neg map
             [] when Flag == 2 -> ?F([]); % case: no mandatory keys in pos map
             X ->
               LabelKeys = u(X),
               Lower = ty_rec:diff(LabelKeys, TyVar),
               Upper = ty_rec:diff(TyVar, LabelKeys),
               ?F(constraint_set:meet(
                 ?F(ty_rec:normalize(Lower, Fixed, M)),
                 ?F(ty_rec:normalize(Upper, Fixed, M))
               ))
           end
       end
        || {A, {Tag, TyVar}} := _ <- Labels1, var_key == Tag]
    )
              end,
  _Constrain_Map1_With_Map2 = C1 = Constrain(TyMap1, TyMap2, 1),
  _Constrain_Map2_With_Map1 = C2 = Constrain(TyMap2, TyMap1, 2),
  ?F(constraint_set:meet(C1, C2)).


filter_empty_labels(Labels) -> maps:filter(
  fun({?OPT, _}, _) -> true;
     ({?MAN, _}, TyRef) -> not ty_rec:is_empty(TyRef)
  end, Labels).
elim_lbl_conflict(_Constraints = C, _Association = A) ->
  case {C, A} of
    {[[]], ?OPT} -> []; % [[]] must only occur with mandatory
    {[], ?OPT} -> [[]]; % ⊥ exists as solution
    _ -> C
  end.
u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
lazy_meet(Cs) -> lists:foldr(fun(C, A) -> ?F(constraint_set:meet(C, A)) end, ?F([[]]), Cs).
