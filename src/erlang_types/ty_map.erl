-module(ty_map).

% TODO explain modules

-define(OPT, optional).
-define(MAN, mandatory).
-define(A, fun(A, ?OPT) -> ?MAN; (A, _) -> A end).

-export([compare/2, equal/2, substitute/4, all_variables/1]).
-export([map/2, b_anymap/0, b_emptymap/0, b_empty/0, b_intersect/2, b_diff/2, pi/2, pi_var/2, pi_tag/2, key_domain/0, key_domain/2, value_domain/1]).

-type ty_map() :: term().
-type ty_ref() :: {ty_ref, integer()}.
-type labels() :: #{ al() => ty_ref() }.
-type steps()  :: #{ key_tag() := ty_ref() }.

-type al() :: {assoc(), l()}.
-type l()  :: {key_tag() | var_tag(), ty_ref()}.

-type key_tag() :: atom_key | integer_key | tuple_key.
-type var_tag() :: var_key.
-type assoc()   :: optional | mandatory.

compare(A, B) when A < B -> -1;
compare(A, B) when A > B -> 1;
compare(_, _) -> 0.
equal(P1, P2) -> compare(P1, P2) =:= 0.

-spec map(labels(), steps()) -> ty_map().
map(Labels, Steps) -> {ty_map, Labels, Steps}.

-spec b_empty() -> ty_map().
b_empty() -> {ty_map, #{}, #{}}.

-spec b_emptymap() -> ty_map().
b_emptymap() ->
  Labels = #{},
  Steps = #{S => ty_rec:empty() || S <- step_names()},
  {ty_map, Labels, Steps}.

-spec b_anymap() -> ty_map().
b_anymap() ->
  Labels = #{},
  Steps = #{S => ty_rec:any() || S <- step_names()},
  {ty_map, Labels, Steps}.


-spec b_intersect(ty_map(), ty_map()) -> ty_map().
b_intersect({ty_map, Ls1, St1} = Map1, Map2 = {ty_map, Ls2, St2}) ->
  StInt  = maps:merge_with(fun(_Step, Ref1, Ref2) -> ty_rec:intersect(Ref1, Ref2) end, St1, St2),
  LsInt1 = maps:map(fun(AL, Ref) -> ty_rec:intersect(Ref, pi_h(AL, Map2)) end, Ls1),
  LsInt2 = maps:map(fun(AL, Ref) -> ty_rec:intersect(Ref, pi_h(AL, Map1)) end, Ls2),
  % can contain opposites
  RawMerge = maps:merge(LsInt1, LsInt2),
  % mandatory is there for all labels
  % optional is there if not the same label as mandatory present
  _Without_Opposite_Associations = LsInt = maps:filter(
    fun({?MAN, _}, _) -> true;
       ({?OPT, L}, _) -> not is_map_key({?MAN, L}, RawMerge)
    end, RawMerge),
  map(LsInt, StInt).


-spec b_diff(ty_map(), ty_map()) -> ty_map().
b_diff({ty_map, Ls1, St1} = Map1, Map2 = {ty_map, Ls2, St2}) ->
  StDiff = maps:merge_with(fun(_Step, Ref1, Ref2) -> ty_rec:diff(Ref1, Ref2) end, St1, St2),
  LsDiff1 = #{begin
                {A2, _} = pi(L, Map2),
                case Tag of
                  var_key -> {?MAN, L}; % for normalization
                  _       -> {?A(A1, A2), L} end
              end
    => ty_rec:diff(
      pi_h(AL, Map1),
      pi_h(AL, Map2)) || AL = {A1, L = {Tag, _}} <- maps:keys(Ls1)
  },
  LsDiff2 = #{begin
                {A1, _} = pi(L, Map1),
                case Tag of
                  var_key -> {?MAN, L}; % for normalization
                  _       -> {?A(A1, A2), L} end
              end
    => ty_rec:diff(
      pi_h(AL, Map1),
      pi_h(AL, Map2)) || AL = {A2, L = {Tag, _}} <- maps:keys(Ls2)
  },
  LsDiff = maps:merge(LsDiff1, LsDiff2),
  map(LsDiff, StDiff).


-spec pi(l(), ty_map()) -> {assoc(), ty_ref()}.
pi(L = {Tag, _}, {ty_map, Labels, Steps}) ->
  case Labels of
    #{{?OPT, L} := Ref} -> {?OPT, Ref};
    #{{?MAN, L} := Ref} -> {?MAN, Ref};
    #{} when var_key == Tag -> {?MAN, ty_rec:empty()};
    #{} -> #{Tag := Ref} = Steps, {?OPT, Ref}
  end.


-spec pi_var(al(), ty_map()) -> ty_ref().
pi_var({?OPT, {var_key, _}}, Map) ->
  value_domain(Map);
pi_var({?MAN, {var_key, _}}, Map = {ty_map, Labels, _}) ->
  case [Ref || {A, _} := Ref <- Labels, ?MAN == A] of
    [] -> value_domain(Map);
    X -> u(X)
  end;
pi_var(AL, {ty_map, Labels, _}) ->
  case Labels of
    #{AL := Ref} -> Ref;
    #{} -> case AL of
             {?OPT, _} -> u([Ref || {A, {Tag, _}} := Ref <- Labels, var_key == Tag, ?OPT == A]);
             {?MAN, _} -> u([Ref || {_, {Tag, _}} := Ref <- Labels, var_key == Tag])
           end
  end.


-spec pi_tag(key_tag(), ty_map()) -> ty_ref().
pi_tag(Tag, {ty_map, Labels, Steps}) ->
  #{Tag := Ref} = Steps,
  Refs = [Ref || {_, {T, _}} := Ref <- Labels, T == Tag],
  u([Ref | Refs]).


-spec key_domain() -> ty_ref().
key_domain() ->
  u([ty_rec:interval(), ty_rec:atom(), ty_rec:tuple()]).


-spec key_domain(ty_map(), WithVariables :: boolean()) -> ty_ref().
key_domain({ty_map, Labels, Steps}, WithVariables) ->
  StepKeys = [step_ty(S) || S := Ref <- Steps, Ref =/= ty_rec:empty()],
  LabelKeys = case WithVariables of
                true ->  [Ref || {_, {_, Ref}} := _ <- Labels];
                false -> [Ref || {_, {Tag, Ref}} := _ <- Labels, var_key =/= Tag]
              end,
  u(StepKeys ++ LabelKeys).


-spec value_domain(ty_map()) -> ty_ref().
value_domain({ty_map, Labels, Steps}) ->
  u([Ref || _ := Ref <- Steps] ++ [Ref || _ := Ref <- Labels]).


substitute(_MkTy, {ty_map, Labels, Steps}, SubstituteMap, Memo) ->
  NewLs = maps:fold(fun({A, {Tag, TyRef1}}, TyRef2, Acc) ->
    S1 = ty_rec:substitute(TyRef1, SubstituteMap, Memo),
    S2 = ty_rec:substitute(TyRef2, SubstituteMap, Memo),
    AL = {A, {Tag, S1}},
    % t := 0 not allowed; maybe infinite := t ?
    % in that case, don't add field
    case ?MAN == A andalso ty_rec:is_empty(S2) of
      true -> Acc;
      false -> Acc#{AL => S2}
    end
                    end, #{}, Labels
  ),
  NewSt = maps:map(fun(_, TyRef) -> ty_rec:substitute(TyRef, SubstituteMap, Memo) end, Steps),

  case maps:size(NewLs) < maps:size(Labels) of
    true -> ty_rec:empty();
    false -> map(NewLs, NewSt)
  end.


all_variables({ty_map, Labels, Steps}) ->
  TySt = [T || _ := T <- Steps],
  TyLsKey = [T || {_, {_, T}} := _ <- Labels],
  TyLsVal = [T || _ := T <- Labels],
  ty_rec:all_variables(TySt) ++ ty_rec:all_variables(TyLsKey) ++ ty_rec:all_variables(TyLsVal).


u(Tys) -> lists:foldr(fun ty_rec:union/2, ty_rec:empty(), Tys).
step_ty(atom_key) -> ty_rec:atom();
step_ty(integer_key) -> ty_rec:interval();
step_ty(tuple_key) -> ty_rec:tuple().
step_names() -> [atom_key, integer_key, tuple_key].
pi_h(AL = {_, L}, Map) -> % helper
  {_, Ref1} = pi(L, Map),
  Ref2 = pi_var(AL, Map),
  u([Ref1, Ref2]).
