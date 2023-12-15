-module(ty_map).

%% Implements quasi k-omega step function interpretation of maps

-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(ADIFF, fun(_, ?OPT) -> ?MAN; (A, _) -> A end).
-define(AINT, fun(A, ?OPT) -> A; (_, ?MAN) -> ?MAN end).

-export([compare/2, equal/2, has_ref/2, substitute/4, transform/2, all_variables/1]).
-export([map/2, big_intersect/1, intersect/2, diff_labels/2, diff_k_steps/2, diff_omega1_step/2, omegas/1, key_variables/1, step_names/0, key_domain/0]).

-record(ty_map, {
  labels :: labels(),
  labels_added :: list({FiniteO1::ty_ref(), W1::use_step | ty_ref()}),
  steps :: k_steps(),
  omegas :: {
    RestrictedO1::ty_ref(),
    RestrictedO2::ty_ref(),
    W1::use_step | ty_ref()
  },
  key_variables :: list({assoc(), TyVar::ty_ref()})
}).

-type ty_map() :: #ty_map{}.
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{ al() => ty_ref() }.
-type k_steps()  :: #{ key_tag() := ty_ref() }.
-type al() :: {assoc(), l()}.
-type l()  :: {key_tag(), ty_ref()}.

-type key_tag() :: atom_key | integer_key | tuple_key.
-type assoc()   :: optional | mandatory.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.


-spec map(X, k_steps()) -> ty_map() when
  X :: #{al() | Y => ty_ref()},
  Y :: {assoc(), {var_key, ty_ref()}}.

map(LabelsVar, Steps) ->
  {Labels, W1, W2, KeyVars} = maps:fold(fun(ALVar, Ref2, {Ls, W1, W2, KeyVars}) ->
    case ALVar of
      {?MAN, {var_key, Ref1}} -> {Ls, union([W1, Ref2]), W2, [{?MAN, Ref1} | KeyVars]};
      {?OPT, {var_key, Ref1}} -> {Ls, W1, union([W2, Ref2]), [{?OPT, Ref1} | KeyVars]};
      _ -> {Ls#{ALVar => Ref2}, W1, W2, KeyVars}
    end
                                        end, {#{}, ty_rec:empty(), ty_rec:empty(), []}, LabelsVar),

  EmptySteps = [S || S := Ref <- Steps, ty_rec:is_empty(Ref)],
  DefinedLabels = [Ref || {_, {_, Ref}} := _ <- Labels],
  StepsWithOmega = maps:merge(Steps, #{S => W2 || S <- EmptySteps}), % w2 embedded in k-steps

  O1 = negate_to_key_domain(union(DefinedLabels)), % restricted
  O2 = ty_rec:intersect(O1, union([step_ty(S) || S <- EmptySteps])), % restricted
  W11 = case ty_rec:is_empty(W1) of
          true -> use_step; % no mandatory key type vars
          false -> W1
        end,
  #ty_map{ labels = Labels, labels_added = [], steps = StepsWithOmega, omegas = {O1, O2, W11}, key_variables = KeyVars }.


-spec big_intersect([ty_map()]) -> ty_map().
big_intersect([]) -> ty_map:map(#{}, #{S => ty_rec:any() || S <- step_names()});
big_intersect([Map | Maps]) -> lists:foldr(fun intersect/2, Map, Maps).


-spec intersect(ty_map(), ty_map()) -> ty_map().
intersect(Map1, Map2) ->
  #ty_map{ steps = Steps1, labels_added = LA1, omegas = {_, O2, W1},  key_variables = KeyVars1 } = Map1,
  #ty_map{ steps = Steps2, labels_added = LA2, omegas = {_, O22, W11},  key_variables = KeyVars2 } = Map2,
  LsInt = labels_apply({fun ty_rec:intersect/2, ?AINT}, Map1, Map2),
  StInt = maps:merge_with(fun(_, Ref1, Ref2) -> ty_rec:intersect(Ref1, Ref2) end, Steps1, Steps2),

  DefinedLabels = [Ref || {_, {_, Ref}} := _ <- LsInt] ++ [Ref || {Ref, _} <- LA1 ++ LA2],

  O1Int = negate_to_key_domain(union(DefinedLabels)), % stays restricted
  O2Int = union([O2, O22]), % stays restricted

  W1Int = case {W1, W11} of
            {use_step, use_step} -> use_step;
            {_, use_step} -> ty_rec:intersect(W1, union([Ref || _ := Ref <- Steps2]));
            {use_step, _} -> ty_rec:intersect(W11, union([Ref || _ := Ref <- Steps1]));
            {_, _} -> ty_rec:intersect(W1, W11)
          end,

  #ty_map{ labels = LsInt, labels_added = LA1 ++ LA2, steps = StInt, omegas = {O1Int, O2Int, W1Int}, key_variables = KeyVars1 ++ KeyVars2 }.


-spec diff_labels(ty_map(), ty_map()) -> labels().
diff_labels(Map1, Map2) -> labels_apply({fun ty_rec:diff/2, ?ADIFF}, Map1, Map2).

labels_apply({IntOrDiff, Assoc}, Map1, Map2) ->
  #ty_map{ labels = Labels1 } = Map1,
  #ty_map{ labels = Labels2 } = Map2,

  LsDiff1 = maps:fold(fun({A1, L}, Ref1, Ls) ->
    {A2, Ref2} = pi(L, Map2),
    AL = {Assoc(A1, A2), L},
    Combined = IntOrDiff(Ref1, Ref2),
    Ls#{AL => Combined}
                      end, #{}, Labels1),

  LsDiff2 = maps:fold(fun({A2, L}, Ref2, Ls) ->
    {A1, Ref1} = pi(L, Map1),
    AL = {Assoc(A1, A2), L},
    Combined = IntOrDiff(Ref1, Ref2),
    Ls#{AL => Combined}
                      end, #{}, Labels2),

  maps:merge(LsDiff1, LsDiff2).


-spec diff_k_steps(ty_map(), ty_map()) -> k_steps().
diff_k_steps(Map1, Map2) ->
  #ty_map{ steps = Steps1 } = Map1,
  #ty_map{ steps = Steps2 } = Map2,
  maps:merge_with(fun(_, Ref1, Ref2) -> ty_rec:diff(Ref1, Ref2) end, Steps1, Steps2).


-spec diff_omega1_step(ty_map(), ty_map()) -> ty_ref().
diff_omega1_step(Map1, Map2) ->
  #ty_map{ steps = Steps1, omegas = {_, _, W1} } = Map1,
  #ty_map{ steps = Steps2, omegas = {_, _, W11} } = Map2,
  case {W1, W11} of
    {use_step, use_step} -> ty_rec:empty();
    {_, use_step} -> ty_rec:diff(W1, union([Ref || _ := Ref <- Steps2]));
    {use_step, _} -> ty_rec:diff(union([Ref || _ := Ref <- Steps1]), W11);
    {_, _} -> ty_rec:diff(W1, W11)
  end.


-spec omegas(ty_map()) -> {ty_ref(), ty_ref()}.
omegas(#ty_map{ omegas = {O1, O2, _} }) -> {O1, O2}.


-spec key_variables(ty_map()) -> list({assoc(), TyVar::ty_ref()}).
key_variables(#ty_map{ key_variables = KeyVars }) -> KeyVars.


-spec pi(l(), ty_map()) -> {assoc(), ty_ref()}.
pi(L = {Tag, Ref1}, Map) ->
  #ty_map{ labels = Labels, labels_added = LA, steps = Steps, omegas = {_, _, W1} } = Map,
  case Labels of
    #{{?OPT, L} := Ref2} -> {?OPT, Ref2};
    #{{?MAN, L} := Ref2} -> {?MAN, Ref2};
    #{} ->
      #{Tag := Ref2} = Steps,
      case [Y || {X, Y} <- LA, ty_rec:is_subtype(Ref1, X)] of
        [] -> case W1 of
                use_step -> {?OPT, Ref2};
                _ -> {?MAN, W1}
              end;
        Ys -> {?MAN, intersect(lists:map(fun(use_step) -> Ref2; (Y) -> Y end, Ys))}
      end
  end.


has_ref(Map, Ref) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1}, key_variables = KeyVars } = Map,
  HasRef = fun({_, {_, Ref1}}, Ref2) -> Ref == Ref1 orelse Ref == Ref2;
              (_, Ref1) -> Ref == Ref1
           end,
  LS = maps:filter(HasRef, maps:merge(Labels, Steps)),
  KV = lists:filter(fun({_, Var}) -> Ref == Var end, KeyVars),

  Ref == W1 orelse maps:size(LS) > 0 orelse length(KV) > 0.


substitute(_MkTy, Map, SubstituteMap, Memo) ->
  #ty_map{ labels = Labels, labels_added = LA, steps = Steps, omegas = {_, O2, W1}, key_variables = KeyVars } = Map,
  SLabels = maps:map(fun(_, Ref) -> ty_rec:substitute(Ref, SubstituteMap, Memo) end, Labels),
  SSteps = maps:map(fun(_, Ref) -> ty_rec:substitute(Ref, SubstituteMap, Memo) end, Steps),
  SW1 = case W1 of use_step -> use_step; _ -> ty_rec:substitute(W1, SubstituteMap, Memo) end,

  {ManVars, OptVars} = lists:partition(fun({?MAN, _}) -> true; ({?OPT, _}) -> false end, KeyVars),
  SubstituteKeyVars = fun(Vars) -> union([ty_rec:substitute(Var, SubstituteMap) || {_, Var} <- Vars]) end,
  Additional = {X, _} = {SubstituteKeyVars(ManVars), SW1},

  DefinedLabels = [X] ++ [Ref || {Ref, _} <- LA] ++ [Ref || {_, {_, Ref}} := _ <- SLabels],

  O11 = ty_rec:negate(union(DefinedLabels)), % restricted
  O22 = ty_rec:diff(O2, SubstituteKeyVars(OptVars)), % restricted
  Rest = lists:filter(fun({_, Var}) -> is_map_key(Var, SubstituteMap) end, KeyVars),

  #ty_map{ labels = SLabels, labels_added = [Additional | LA], steps = SSteps, omegas = {O11, O22, use_step}, key_variables = Rest }.


transform(Map, #{to_map := ToMap}) ->
  #ty_map{ labels = Labels, labels_added = LA, steps = Steps, omegas = {_, _, W1}, key_variables = KeyVars } = Map,
  {ManLs, OptLs} = lists:partition(fun({{?MAN, _}, _}) -> true; ({?OPT, _}) -> false end, maps:to_list(Labels)),

  ManAssoc = [{Ref1, Ref2} || {{_, {_, Ref1}}, Ref2} <- ManLs] ++ LA ++ [{Var, W1} || {A, Var} <- KeyVars, A == ?MAN],
  OptAssoc = [{Ref1, Ref2} || {{_, {_, Ref1}}, Ref2} <- OptLs] ++ [{step_ty(S), Ref} || S := Ref <- Steps],

  ToMap(ManAssoc, OptAssoc).


all_variables(Map) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1}, key_variables = KeyVars } = Map,
  LabelVars = [ty_rec:all_variables(Ref) || _ := Ref <- Labels],
  StepVars = [ty_rec:all_variables(Ref) || _ := Ref <- Steps],
  lists:uniq(ty_rec:all_variables(W1) ++ [Var || {_, Var} <- KeyVars] ++ lists:flatten(LabelVars ++ StepVars)).


union(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
intersect(Tys) -> lists:foldr(fun ty_rec:intersect/2, ty_rec:any(), Tys).
step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().
step_names() -> [atom_key, integer_key, tuple_key].
key_domain() -> union([ty_rec:interval(), ty_rec:atom(), ty_rec:tuple()]).
negate_to_key_domain(Ref) -> ty_rec:diff(key_domain(), Ref).