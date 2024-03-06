-module(ty_map).

%% Implements quasi k-omega step function interpretation of maps

-define(OPT, optional).
-define(MAN, mandatory).
-define(F(Z), fun() -> Z end).
-define(ASSOC_DIFF, fun(_, ?OPT) -> ?MAN; (A, _) -> A end).
-define(ASSOC_INT, fun(A, ?OPT) -> A; (_, ?MAN) -> ?MAN end).

-export([compare/2, equal/2, has_ref/2, substitute/3, transform/2, all_variables/1]).
-export([map/2, big_intersect/1, intersect/2, diff_labels/2, diff_steps/2, diff_w1/2, key_variable_suite/1, step_names/0, key_domain/0]).
-import(maps, [to_list/1, keys/1, values/1]).
-export_type([l/0]).

-record(ty_map, { labels :: labels(),
                  steps  :: steps(),
                  omegas :: {
                    O1 :: ty_ref(),
                    O2 :: ty_ref(),
                    W1 :: use_step | ty_ref()
                  },
                  key_variables :: {
                    ManKeyVarUnion :: ty_ref(),
                    OptKeyVarUnion :: ty_ref()
                  }
                }).

-type ty_map() :: #ty_map{}.
-type ty_ref() :: {ty_ref, integer()}.

-type labels() :: #{ al() => ty_ref() }.
-type steps()  :: #{ key_tag() := ty_ref() }.
-type al() :: {assoc(), l()}.
-type l()  :: {key_tag(), ty_ref()}.

-type key_tag() :: atom_key | integer_key | tuple_key.
-type assoc()   :: optional | mandatory.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.


-spec map(X, steps()) -> ty_map() when
  X :: #{al() | Y => ty_ref()},
  Y :: {assoc(), {var_key, ty_ref()}}.

map(LabelsVar, Steps) ->
  {Labels, W1, W2, KeyVars} = maps:fold(fun(ALVar, Ref2, {Ls, W1, W2, K = {ManVarUnion, OptVarUnion}}) ->
    case ALVar of
      {?MAN, {var_key, Ref1}} -> {Ls, union([W1, Ref2]), W2, {union([Ref1, ManVarUnion]), OptVarUnion}};
      {?OPT, {var_key, Ref1}} -> {Ls, W1, union([W2, Ref2]), {ManVarUnion, union([Ref1, OptVarUnion])}};
      _ -> {Ls#{ALVar => Ref2}, W1, W2, K}
    end
                                        end, {#{}, ty_rec:empty(), ty_rec:empty(), {ty_rec:empty(), ty_rec:empty()}}, LabelsVar),

  EmptySteps = [S || {S, Ref} <- to_list(Steps), ty_rec:is_empty(Ref)],
  StepsWithOmega = maps:merge(Steps, maps:from_keys(EmptySteps, W2)), % w2 embedded in steps

  O1 = o1(Labels),
  O2 = o2(O1, Steps),
  W11 = case ty_rec:is_empty(W1) of
          true -> use_step; % no mandatory key type vars
          false -> W1
        end,

  #ty_map{ labels = Labels, steps = StepsWithOmega, omegas = {O1, O2, W11}, key_variables = KeyVars }.


-spec big_intersect([ty_map()]) -> ty_map().
big_intersect([]) -> ty_map:map(#{}, maps:from_keys(step_names(), ty_rec:any()));
big_intersect([Map | Maps]) -> lists:foldr(fun intersect/2, Map, Maps).


-spec intersect(ty_map(), ty_map()) -> ty_map().
intersect(Map1, Map2) ->
  #ty_map{ steps = Steps1, omegas = {_O1, _O2, W1},  key_variables = {ManU1, OptU1} } = Map1,
  #ty_map{ steps = Steps2, omegas = {_O11, _O22, W11},  key_variables = {ManU2, OptU2} } = Map2,
  LsInt = intersect_labels(Map1, Map2),
  StInt = maps:merge_with(fun(_, Ref1, Ref2) -> ty_rec:intersect(Ref1, Ref2) end, Steps1, Steps2),

  O1Int = o1(LsInt), % = O1 U O11
  O2Int = o2(O1Int, StInt), % = O2 U O22
  W1Int = case {W1, W11} of
            {use_step, use_step} -> use_step;
            {_, use_step} -> ty_rec:intersect(W1, union(values(Steps2)));
            {use_step, _} -> ty_rec:intersect(W11, union(values(Steps1)));
            {_, _} -> ty_rec:intersect(W1, W11)
          end,
  KeyVars = {union([ManU1, ManU2]), union([OptU1, OptU2])},

  #ty_map{ labels = LsInt, steps = StInt, omegas = {O1Int, O2Int, W1Int}, key_variables = KeyVars }.


-spec diff_labels(ty_map(), ty_map()) -> labels().
diff_labels(Map1, Map2) -> labels_apply({fun ty_rec:diff/2, ?ASSOC_DIFF}, Map1, Map2).

-spec intersect_labels(ty_map(), ty_map()) -> labels().
intersect_labels(Map1, Map2) -> labels_apply({fun ty_rec:intersect/2, ?ASSOC_INT}, Map1, Map2).


labels_apply({Combiner, Associate}, Map1, Map2) ->
  #ty_map{ labels = Labels1 } = Map1,
  #ty_map{ labels = Labels2 } = Map2,

  LsDiff1 =
    maps:fold(
      fun({A1, L}, Ref1, Ls) ->
        {A2, Ref2} = pi(L, Map2),
        AL = {Associate(A1, A2), L},
        Ls#{AL => Combiner(Ref1, Ref2)}
      end,
      #{}, Labels1),

  LsDiff2 =
    maps:fold(
      fun({A2, L}, Ref2, Ls) ->
        {A1, Ref1} = pi(L, Map1),
        AL = {Associate(A1, A2), L},
        Ls#{AL => Combiner(Ref1, Ref2)}
      end,
      #{}, Labels2),

  maps:merge(LsDiff1, LsDiff2).


-spec diff_steps(ty_map(), ty_map()) -> steps().
diff_steps(Map1, Map2) ->
  #ty_map{ steps = Steps1 } = Map1,
  #ty_map{ steps = Steps2 } = Map2,
  maps:merge_with(fun(_, Ref1, Ref2) -> ty_rec:diff(Ref1, Ref2) end, Steps1, Steps2).


-spec diff_w1(ty_map(), ty_map()) -> ty_ref().
diff_w1(Map1, Map2) ->
  % TODO imp detail: explain why labels diff instead of steps diff
  #ty_map{ labels = Labels1, omegas = {_, _, W1} } = Map1,
  #ty_map{ labels = Labels2, omegas = {_, _, W11} } = Map2,
  case {W1, W11} of
    {use_step, use_step} -> ty_rec:empty();
    {_, use_step} -> ty_rec:diff(W1, union(values(Labels2)));
    {use_step, _} -> ty_rec:diff(union(values(Labels1)), W11);
    {_, _} -> ty_rec:diff(W1, W11)
  end.


-spec key_variable_suite(ty_map()) -> {ty_ref(), ty_ref(), ty_ref(), ty_ref()}.
key_variable_suite(#ty_map{ omegas = {O1, O2, _}, key_variables = {ManU, OptU} }) -> {O1, O2, ManU, OptU}.


-spec pi(l(), ty_map()) -> {assoc(), ty_ref()}.
pi(L = {Tag, _}, Map) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1} } = Map,
  case Labels of
    #{{?OPT, L} := Ref} -> {?OPT, Ref};
    #{{?MAN, L} := Ref} -> {?MAN, Ref};
    #{} ->
      #{Tag := Ref} = Steps,
      case W1 of use_step -> {?OPT, Ref}; _ -> {?MAN, W1} end
  end.


has_ref(Map, Ref) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1} } = Map,
  HasRef = fun({_, {_, Ref1}}, Ref2) -> Ref == Ref1 orelse Ref == Ref2;
              (_, Ref1) -> Ref == Ref1
           end,
  LS = maps:filter(HasRef, maps:merge(Labels, Steps)),

  Ref == W1 orelse maps:size(LS) > 0.


substitute(Map, SubstituteMap, Memo) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1}, key_variables = {ManU, OptU} } = Map,
  SLabels = maps:map(fun(_, Ref) -> ty_rec:substitute(Ref, SubstituteMap, Memo) end, Labels),
  SSteps  = maps:map(fun(_, Ref) -> ty_rec:substitute(Ref, SubstituteMap, Memo) end, Steps),
  SW1     = case W1 of
              use_step -> use_step;
              _ -> ty_rec:substitute(W1, SubstituteMap, Memo)
            end,

  % either all variables substituted or none of them
  SManKeyVars = ty_rec:substitute(ManU, SubstituteMap, Memo),
  % invariant: ManLabels = []  IFF  (W1 = use_step OR ManU does not substitute)
  ManLabels = [{?MAN, L} || L <- ty_rec:to_labels(SManKeyVars)],
  % update happens if W1 =/= use_step
  LabelsUpd = maps:merge(SLabels, maps:from_keys(ManLabels, SW1)),

  SOptKeyVars = ty_rec:substitute(OptU, SubstituteMap, Memo),
  NotAvailable = [S || S <- step_names(), ty_rec:is_empty(ty_rec:intersect(step_ty(S), SOptKeyVars))],
  StepsUpd = maps:merge(SSteps, maps:from_keys(NotAvailable, ty_rec:empty())), % not type checkable unless n-element list types present

  O11 = o1(LabelsUpd),
  O22 = o2(O11, StepsUpd),
  W11 = case ManLabels of [] -> SW1; _ -> use_step end,
  KeyVars = {ty_rec:intersect(ManU, SManKeyVars), ty_rec:intersect(OptU, SOptKeyVars)},

  #ty_map{ labels = LabelsUpd, steps = StepsUpd, omegas = {O11, O22, W11}, key_variables = KeyVars }.


transform(Map, #{to_map := ToMap}) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1}, key_variables = {ManU, _} } = Map,

  {ManLs, OptLs} = lists:partition(
    fun ({{?MAN, _}, _}) -> true;
        ({{?OPT, _}, _}) -> false
    end,
    to_list(Labels)),

  ManKeyVars = case ty_rec:is_empty(ManU) of
                 true -> [];
                 false -> [{ManU, W1}]
               end,

  ManAssoc = [{Ref1, Ref2} || {{_, {_, Ref1}}, Ref2} <- ManLs] ++ ManKeyVars,
  OptAssoc = [{Ref1, Ref2} || {{_, {_, Ref1}}, Ref2} <- OptLs] ++ [{step_ty(S), Ref} || {S, Ref} <- to_list(Steps)],

  ToMap(ManAssoc, OptAssoc).


all_variables(Map) ->
  #ty_map{ labels = Labels, steps = Steps, omegas = {_, _, W1}, key_variables = {ManU, OptU} } = Map,
  LabelVars = lists:map(fun ty_rec:all_variables/1, values(Labels)),
  StepVars = lists:map(fun ty_rec:all_variables/1, values(Steps)),
  ty_rec:all_variables(W1)
  ++ ty_rec:all_variables(ManU)
    ++ ty_rec:all_variables(OptU)
    ++ lists:flatten(LabelVars ++ StepVars).


union(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().
step_names() -> [atom_key, integer_key, tuple_key].
key_domain() -> union([ty_rec:interval(), ty_rec:atom(), ty_rec:tuple()]).
negate_to_key_domain(Ref) -> ty_rec:diff(key_domain(), Ref).
o1(Labels) ->
  negate_to_key_domain(union([Ref || {_, {_, Ref}} <- keys(Labels)])).
o2(O1, Steps) ->
  ty_rec:intersect(O1,
    union([step_ty(S) || {S, Ref} <- to_list(Steps), ty_rec:is_empty(Ref)])).
