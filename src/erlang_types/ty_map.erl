-module(ty_map).

% Implements the (~K)-Comprehension of maps

-define(MAN, mandatory).
-define(OPT, optional).
-define(VAR, variable).

-export([compare/2, equal/2, has_ref/2, substitute/3, transform/2, all_variables/1]).
-export([anymap/1, emptymap/0, map/2, big_intersect/1, intersect/2, pi/2, step_names/0]).
-export([comprehend_diff/2, field_diff/2, field_empty/1, field_normalize/3]).
-export_type([label/0]).

-record(extension, {
  labels :: label_map(),
  steps  :: indexed_step_map(),
  pre :: UnionOfSteps :: ty_ref(), % present steps = steps that are not mapped to empty
  alpha_beta :: {A :: ty_ref(), B :: ty_ref()},
  t_alpha_beta :: {TA :: ty_ref(), TB :: ty_ref()}
}).

-type ty_map() :: #extension{}.
-type ty_ref() :: {ty_ref, integer()}.

-type label_map() :: #{label() => field()}.
-type indexed_step_map()  :: #{{index(), step()} := field()}.

-type label_var_map() :: #{label() | label_var() => field()}.
-type step_map() :: #{step() => field()}.

-type label() :: {step(), ty_ref()}.
-type label_var() :: {variable, ty_ref()}.
-type field() :: {assoc(), ty_ref()}.

-type step() :: integers | atoms | tuples.
-type assoc() :: mandatory | optional.
-type index() :: 'L' | 'LHat'.


compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.


-spec anymap(label_map()) -> ty_map().
anymap(Ls) ->
  % Shorthand for <<ty_map:map(Ls, #{any => any})>>
  St = maps:from_keys(lists:flatten([[{'L', S}, {'LHat', S}] || S <- step_names()]), {?OPT, ty_rec:any()}),
  Pre = union_all([step_ty(S) || S <- step_names()]),
  E = ty_rec:empty(),
  #extension{ labels = Ls, steps = St, pre = Pre, alpha_beta = {E, E}, t_alpha_beta = {E, E} }.

-spec emptymap() -> ty_map().
emptymap() ->
  % Shorthand for <<ty_map:map(#{}, #{any => empty})>>
  E = ty_rec:empty(),
  St = maps:from_keys(lists:flatten([[{'L', S}, {'LHat', S}] || S <- step_names()]), {?OPT, E}),
  #extension{ labels = #{}, steps = St, pre = E, alpha_beta = {E, E}, t_alpha_beta = {E, E} }.


-spec map(label_var_map(), step_map()) -> ty_map().
map(Labels, Steps) ->
  LFolder =
    fun(L, Fld, {Ls, MVars, OVars}) ->
      case {L, Fld} of
        {{?VAR, VarRef}, {?MAN, FRef}} -> {Ls, MVars#{VarRef => FRef}, OVars};
        {{?VAR, VarRef}, {?OPT, FRef}} -> {Ls, MVars, OVars#{VarRef => FRef}};
        {_, _} -> {Ls#{L => Fld}, MVars, OVars}
      end
    end,

  {LabelMap, ManKVars, OptKVars} = maps:fold(LFolder, {#{}, #{}, #{}}, Labels),

  Alpha = union_all(maps:keys(ManKVars)), TAlpha = union_all(maps:values(ManKVars)),
  Beta = union_all(maps:keys(OptKVars)), TBeta = union_all(maps:values(OptKVars)),

  StepsLHat = maps:merge(
    maps:from_keys([{'LHat', S} || S <- step_names()], {?OPT, TBeta}),
    maps:from_list([{{'LHat', S}, {?OPT, Ref}} || {S, Ref} <- maps:to_list(Steps)])
  ),
  StepsL =
    case ty_rec:is_empty(Alpha) of
      true -> maps:from_list([{{'L', S}, V} || {{_, S}, V} <- maps:to_list(StepsLHat)]);
      false -> maps:from_keys([{'L', S} || S <- step_names()], {?MAN, TAlpha})
    end,

  #extension{ labels = LabelMap, steps = maps:merge(StepsL, StepsLHat),
    pre = union_all([step_ty(S) || {S, Ref} <- maps:to_list(Steps), not ty_rec:is_empty(Ref)]),
    alpha_beta = {Alpha, Beta},
    t_alpha_beta = {TAlpha, TBeta}
  }.


-spec big_intersect([ty_map()]) -> ty_map().
big_intersect([]) -> ty_map:anymap(#{});
big_intersect([Map | Maps]) -> lists:foldr(fun intersect/2, Map, Maps).


-spec intersect(ty_map(), ty_map()) -> ty_map().
intersect(Map1, Map2) ->
  #extension{ labels = Ls1, steps = St1, pre = Pre1, alpha_beta = {Alpha1, Beta1}, t_alpha_beta = {TA1, TB1} } = Map1,
  #extension{ labels = Ls2, steps = St2, pre = Pre2, alpha_beta = {Alpha2, Beta2}, t_alpha_beta = {TA2, TB2} } = Map2,

  AllLabels = maps:keys(Ls1) ++ maps:keys(Ls2),
  Ls3 = maps:from_list([{L, field_intersect(pi(L, Map1), pi(L, Map2))} || L <- AllLabels]),
  St3 = maps:intersect_with(fun(_IndexedStep, Fld1, Fld2) -> field_intersect(Fld1, Fld2) end, St1, St2),

  #extension{ labels = Ls3, steps = St3,
    pre = ty_rec:intersect(Pre1, Pre2),
    alpha_beta = {ty_rec:intersect(Alpha1, Alpha2), ty_rec:intersect(Beta1, Beta2)},
    t_alpha_beta = {ty_rec:intersect(TA1, TA2), ty_rec:intersect(TB1, TB2)}
  }.


-spec comprehend_diff(ty_map(), ty_map()) -> {label_map(), indexed_step_map(), Y1 :: ty_ref(), Y2 :: ty_ref()}.
comprehend_diff(Map1, Map2) ->
  % Y1 = -(A v La), Y2 = A v La v Lb v B v steps
  #extension{ labels = Ls1, steps = St1, pre = Pre1, alpha_beta = {Alpha1, Beta1} } = Map1,
  #extension{ labels = Ls2, steps = St2, pre = Pre2, alpha_beta = {Alpha2, Beta2} } = Map2,

  AllLabels = maps:keys(Ls1) ++ maps:keys(Ls2),
  Ls3 = maps:from_list([{L, field_diff(pi(L, Map1), pi(L, Map2))} || L <- AllLabels]),
  St3 = maps:intersect_with(fun(_IndexedStep, Fld1, Fld2) -> field_diff(Fld1, Fld2) end, St1, St2),

  {ManLs1, OptLs1} = partition_labels(Ls1),
  {ManLs2, OptLs2} = partition_labels(Ls2),
  Param1Y1 = ty_rec:negate(union_all([Alpha1] ++ [LRef || {{_, LRef}, _} <- ManLs1])),
  Param1Y2 = union_all([ty_rec:negate(Param1Y1), Beta1] ++ [LRef || {{_, LRef}, _} <- OptLs1]),

  Param2Y1 = ty_rec:negate(union_all([Alpha2] ++ [LRef || {{_, LRef}, _} <- ManLs2])),
  Param2Y2 = union_all([ty_rec:negate(Param2Y1), Beta2] ++ [LRef || {{_, LRef}, _} <- OptLs2]),

  {Ls3, St3, ty_rec:diff(Param1Y1, Param2Y1), ty_rec:diff(ty_rec:union(Param1Y2, ty_rec:diff(Pre1, Pre2)), ty_rec:union(Param2Y2, ty_rec:diff(Pre2, Pre1)))}.


-spec pi(label(), ty_map()) -> field().
pi(L = {Step, _}, Map) ->
  #extension{ labels = Ls, steps = St } = Map,
  case Ls of
    #{L := Fld} -> Fld;
    #{} -> #{{'L', Step} := Fld} = St, Fld
  end.


has_ref(Map, Ref) ->
  #extension{ labels = Ls, steps = St, alpha_beta = {Alpha, Beta} } = Map,
  F1 = [X || X = {{_, LRef}, {_, FRef}} <- maps:to_list(Ls), Ref == LRef orelse Ref == FRef],
  F2 = [X || X = {_, {_, FRef}} <- maps:to_list(St), Ref == FRef],
  F1 ++ F2 /= [] orelse Alpha == Ref orelse Beta == Ref.


substitute(Map, SubstituteMap, Memo) ->
  #extension{ labels = Ls, steps = St, pre = Pre, alpha_beta = {Alpha, Beta}, t_alpha_beta = {TA, TB} } = Map,
  LsSub = maps:map(fun(_, {Assoc, FRef}) -> {Assoc, ty_rec:substitute(FRef, SubstituteMap, Memo)} end, Ls),
  StSub = maps:map(fun(_, {Assoc, FRef}) -> {Assoc, ty_rec:substitute(FRef, SubstituteMap, Memo)} end, St),
  ManLs = ty_rec:take_labels(AlphaSub = ty_rec:substitute(Alpha, SubstituteMap, Memo)),
  OptLs = ty_rec:take_labels(BetaSub = ty_rec:substitute(Beta, SubstituteMap, Memo)),

  %% Labels %%
  NewManLs = [{L, maps:get({'L', Step}, StSub)} || {Step, _} = L <- ManLs],
  NewOptLs = [{L, maps:get({'LHat', Step}, StSub)} || {Step, _} = L <- OptLs],
  NewLs = maps:merge(LsSub, maps:from_list(NewManLs ++ NewOptLs)),

  %% Steps, Key Variables %%
  % Which steps are out in optional key var substitution
  NotSubtypeSteps = [S || S <- step_names(), not ty_rec:is_subtype(step_ty(S), ty_rec:union(BetaSub, Pre))],
  MkEmpty = fun(I) -> [{{I, S}, {?OPT, ty_rec:empty()}} || S <- NotSubtypeSteps] end,
  {NewSt, NewAlpha, NewBeta} =
    case ty_rec:is_subtype(AlphaSub,
      union_all([LRef || {_, LRef} <- ManLs])) of
      true ->
        % Alpha has label upper bound (A = MuAlpha n (l1|...|ln) )
        % Assume MuAlpha = any
        Empty = maps:from_list(MkEmpty('L') ++ MkEmpty('LHat')),
        {maps:merge(mk_equal_steps(StSub), Empty), ty_rec:empty(), BetaSub};
      false ->
        % A = MuAlpha n (A1|...|AM | l1|...|lN)
        Empty = maps:from_list(MkEmpty('LHat')),
        {maps:merge(StSub, Empty), AlphaSub, BetaSub}
    end,

  #extension{labels = NewLs, steps = NewSt,
    pre = union_all([Pre] ++ [step_ty(S) || S <- step_names() -- NotSubtypeSteps]),
    alpha_beta = {NewAlpha, NewBeta},
    t_alpha_beta = {ty_rec:substitute(TA, SubstituteMap, Memo), ty_rec:substitute(TB, SubstituteMap, Memo)}
  }.


transform(Map, #{to_map := ToMap}) ->
  #extension{ labels = Ls, steps = St, pre = Pre, alpha_beta = {Alpha, Beta}, t_alpha_beta = {TA, TB} } = Map,
  {ManLs, OptLs} = partition_labels(Ls),
  PreSt = [S || S <- step_names(), ty_rec:is_subtype(step_ty(S), Pre)],

  ManMappings = [{LRef, FRef} || {{_Kind, LRef}, {_Assoc, FRef}} <- ManLs]
    ++ case ty_rec:is_empty(Alpha) of true -> []; false -> [{Alpha, TA}] end,

  OptMappings = [{LRef, FRef} || {{_Kind, LRef}, {_Assoc, FRef}} <- OptLs]
    ++ case ty_rec:is_empty(Beta) of true -> []; false -> [{Beta, TB}] end
    ++ [{step_ty(S), begin {_, FRef} = maps:get({'LHat', S}, St), FRef end} || S <- PreSt],

  ToMap(ManMappings, OptMappings).


all_variables(Map) ->
  #extension{ labels = Ls, steps = St, alpha_beta = {Alpha, Beta} } = Map,
  ty_rec:all_variables(Alpha)
  ++ ty_rec:all_variables(Beta)
    ++ lists:flatten([ty_rec:all_variables(Ref) || {_, Ref} <- maps:values(Ls) ++ maps:values(St)]).


union_all(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
step_ty(atoms) -> ty_rec:atom();
step_ty(integers) -> ty_rec:interval();
step_ty(tuples) -> ty_rec:tuple().
step_names() -> [atoms, integers, tuples]. % sequence matters
%%key_domain() -> union_all([ty_rec:atom(), ty_rec:interval(), ty_rec:tuple()]).
mk_equal_steps(St) -> maps:map(fun({_I, S}, _) -> maps:get({'LHat', S}, St) end, St).
partition_labels(Ls) -> lists:partition(fun({_, {?MAN, _}}) -> true; ({_, {?OPT, _}}) -> false end, maps:to_list(Ls)).

field_intersect({?OPT, Ref1}, {Assoc, Ref2}) -> {Assoc, ty_rec:intersect(Ref1, Ref2)};
field_intersect({?MAN, _}, {?OPT, _}) -> {?MAN, ty_rec:empty()};
field_intersect({?MAN, Ref1}, {_, Ref2}) -> {?MAN, ty_rec:intersect(Ref1, Ref2)}.
field_diff({?MAN, Ref1}, {_, Ref2}) -> {?MAN, ty_rec:diff(Ref1, Ref2)};
field_diff({?OPT, Ref1}, {?MAN, Ref2}) -> {?OPT, ty_rec:diff(Ref1, Ref2)};
field_diff({?OPT, Ref1}, {?OPT, Ref2}) -> {?MAN, ty_rec:diff(Ref1, Ref2)}.

field_empty({?OPT, _}) -> false;
field_empty({?MAN, Ref}) -> ty_rec:is_empty(Ref).
field_normalize({?OPT, _}, _, _) -> [[]];
field_normalize({?MAN, Ref}, Fixed, M) -> ty_rec:normalize(Ref, Fixed, M).