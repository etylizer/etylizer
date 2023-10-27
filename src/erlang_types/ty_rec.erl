-module(ty_rec).

-define(F(Z), fun() -> Z end).


-export([empty/0, any/0]).
-export([union/2, negate/1, intersect/2, diff/2, is_any/1]).
-export([is_empty/1, extract_variables/1]).

% additional type constructors
-export([predef/0, predef/1, variable/1, atom/1, interval/1, tuple/2]).
% type constructors with type refs
-export([list/1, function/2]).
% top type constructors
-export([list/0, function/0, atom/0, interval/0, tuple/0, ty_of/6]).

-export([is_equivalent/2, is_subtype/2, normalize/3]).

-export([substitute/2, substitute/3, pi/2, all_variables/1]).

-export([transform/2, print/1]).

-record(ty, {predef, atom, interval, list, tuple, function}).

-type ty_ref() :: {ty_ref, integer()}.
-type interval() :: term().
%%-type ty_tuple() :: term().
%%-type ty_function() :: term().
-type ty_variable() :: term().
-type ty_atom() :: term().


% ======
% top-level API
% ======
print(Ref) -> pretty:render_ty(ast_lib:erlang_ty_to_ast(Ref)) .

ty_of(Predef, Atom, Int, List, Tuple, Function) ->
  #ty{predef = Predef, atom = Atom, interval = Int, list = List, tuple = Tuple, function = Function}.

is_subtype(TyRef1, TyRef2) ->
  NewTy = intersect(TyRef1, ty_rec:negate(TyRef2)),

  is_empty(NewTy).

is_equivalent(TyRef1, TyRef2) ->
  is_subtype(TyRef1, TyRef2) andalso is_subtype(TyRef2, TyRef1).

maybe_intersect(Z2, Other, Intersect) ->
  case subty:is_subty(symtab:empty(), Z2, Other) of %TODO symtab?
    true -> Z2;
    false -> Intersect([Other, Z2])
  end.

transform(TyRef, Ops =
  #{
    any_list := Lists,
    any_tuple := Tuples,
    any_function := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    any_predef := Predef,
    union := Union,
    intersect := Intersect,
    negate := Negate,
    var := Var
  }) ->
  % Do things twice, pos and neg
  Pos = transform_p(TyRef, Ops),
  Neg = transform_p(ty_rec:negate(TyRef), Ops),

%%  io:format(user, "Positive:~n~p~n", [Pos]),
%%  io:format(user, "Negative:~n~p~n", [Neg]),
  % very dumb heuristic: smaller is better
  case size(term_to_binary(Pos)) > size(term_to_binary(Neg)) of
    false -> {pos, Pos};
    _ -> {neg, Neg}
  end.
%%  {neg, Neg}.
%%  {pos, Pos}.

transform_p(TyRef, Ops =
  #{
    any_list := Lists,
    any_tuple := Tuples,
    any_function := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    any_predef := Predef,
    union := Union,
    intersect := Intersect,
    negate := Negate,
    var := Var
  }) ->
%%  io:format(user,"<~p> Transforming: ~p~n~p~n", [Ref = make_ref(), TyRef, ty_ref:load(TyRef)]),
  DnfMap = prepare(TyRef),
%%  io:format(user, "<~p> Prepared: ~n~p~n", [Ref, DnfMap]),

  Mapped = maps:map(fun({Pv, Nv}, TyR) ->
    NewVars = lists:map(fun(K) -> Var(K) end, Pv),
    NewVarsN = lists:map(fun(K) -> Negate(Var(K)) end, Nv),
    case ty_rec:is_subtype(ty_rec:any(), TyR) of
      true ->
        Intersect(NewVars ++ NewVarsN);
      _ ->
        #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T}, function = {DF, F}} = ty_ref:load(TyR),
        NP = maybe_intersect(dnf_var_predef:transform(P, Ops), Predef(), Intersect),
        NA = maybe_intersect(dnf_var_ty_atom:transform(A, Ops), Atoms(), Intersect),
        NI = maybe_intersect(dnf_var_int:transform(I, Ops), Intervals(), Intersect),
        NL = maybe_intersect(dnf_var_ty_list:transform(L, Ops), Lists(), Intersect),

        Z1 = multi_transform(DT, T, Ops),
        NT = maybe_intersect(Z1, Tuples(), Intersect),
        %NT = Intersect([Tuples(), Z1]),

        Z2 = multi_transform_fun(DF, F, Ops),
        NF = maybe_intersect(Z2, Functions(), Intersect),
        %NF = Intersect([Functions(), Z2]),
        Intersect(NewVars ++ NewVarsN ++ [Union([NP, NA, NI, NL, NT, NF])])
    end
           end, DnfMap),

  Ety = Union(maps:values(Mapped)),
%%  io:format(user,"<~p> Result: ~p~n", [Ref, Ety]),
  Sanity = ast_lib:ast_to_erlang_ty(Ety),
%%  io:format(user,"<~p> Sanity: ~p~n", [Ref, Sanity]),
  case is_equivalent(TyRef, Sanity) of
    true -> ok;
    false ->
      io:format(user, "--------~n", []),
      io:format(user, "~p~n", [ty_ref:load(TyRef)]),
      io:format(user, "~p~n", [Ety]),
      error(todo)
  end,
  Ety.

prepare(TyRef) ->
  #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T}, function = {DF, F}} = ty_ref:load(TyRef),
  VarMap = #{},

  PDnf = dnf_var_predef:get_dnf(P),
  ADnf = dnf_var_ty_atom:get_dnf(A),
  IDnf = dnf_var_int:get_dnf(I),
  LDnf = dnf_var_ty_list:get_dnf(L),

  PMapped = lists:map(fun({Pv, Nv, T}) -> {{Pv, Nv}, ty_rec:predef(dnf_var_predef:predef(T))} end, PDnf),
  AMapped = lists:map(fun({Pv, Nv, T}) -> {{Pv, Nv}, ty_rec:atom(dnf_var_ty_atom:ty_atom(T))} end, ADnf),
  IMapped = lists:map(fun({Pv, Nv, T}) -> {{Pv, Nv}, ty_rec:interval(dnf_var_int:int(T))} end, IDnf),
  LMapped = lists:map(fun({Pv, Nv, T}) -> {{Pv, Nv}, ty_rec:list(dnf_var_ty_list:list(T))} end, LDnf),


  TupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple({default, maps:keys(T)}, dnf_var_ty_tuple:tuple(Tp))} end, dnf_var_ty_tuple:get_dnf(DT)),
  TupleExplicitMapped = lists:flatten(lists:map(fun({Size, Tuple}) ->
    DnfTuples = dnf_var_ty_tuple:get_dnf(Tuple),
    _DnfTupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(Tp))} end, DnfTuples)
                                  end, maps:to_list(T))),

  FunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function({default, maps:keys(F)}, dnf_var_ty_function:function(Tp))} end, dnf_var_ty_function:get_dnf(DF)),
  FunctionExplicitMapped = lists:map(fun({Size, Function}) ->
    DnfFunctions = dnf_var_ty_function:get_dnf(Function),
    _DnfFunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function(Size, dnf_var_ty_function:function(Tp))} end, DnfFunctions)
                                     end, maps:to_list(F)),

  AllKinds = lists:flatten([PMapped, AMapped, IMapped, LMapped, TupleMapped, FunctionMapped, TupleExplicitMapped, FunctionExplicitMapped]),

  UpdateKey = fun(_Key, Ty1, Ty2) -> ty_rec:union(Ty1, Ty2) end,
  AllUnions = lists:foldl(fun({VarKey, Ty}, CurrentMap) ->
    NewMap = #{VarKey => Ty},
    maps:merge_with(UpdateKey, CurrentMap, NewMap)
                          end, VarMap, AllKinds),


%%  io:format(user,"All unions;~n~p~n", [AllUnions]),
  SubsumedUnions = maps:fold(fun({Pv, Nv}, Ty, CurrentMap) ->
    subsume_variables(Pv, Nv, Ty, CurrentMap)
                             end, AllUnions, AllUnions),

  SubsumedUnions2 = maps:fold(fun({Pv, Nv}, Ty, CurrentMap) ->
    subsume_coclauses(Pv, Nv, Ty, CurrentMap)
                             end, SubsumedUnions, SubsumedUnions),

%%  io:format(user, "All: ~n~p~n", [AllUnions]),
%%  io:format(user, "Subsumed: ~n~p~n", [SubsumedUnions]),
%%  io:format(user, "Subsumed all: ~n~p~n", [SubsumedUnions2]),



  % Distribute top types to all variables redundantly, if any
  % atom() | a & (Any \ atom)
  % => atom() | a
  TopTypes = [ty_rec:atom(), ty_rec:interval(), ty_rec:tuple(), ty_rec:function(), ty_rec:list(), ty_rec:predef()],
  NoVarsType = maps:get({[], []}, SubsumedUnions2, ty_rec:empty()),

  RedundantUnions = lists:foldl(fun(Top, Acc) ->
    case ty_rec:is_subtype(Top, NoVarsType) of
      true ->
        maps:map(fun(_, V) -> ty_rec:union(Top, V) end, Acc);
      _ -> Acc
    end
                                end, SubsumedUnions2, TopTypes),


  RedundantUnions.


subsume_variables(Pv, Nv, T, VarMap) ->
  maps:fold(fun({Pv1, Nv1}, T1, CurrentMap) ->
    case {Pv1, Nv1, T1} of
      {Pv, Nv, T} -> CurrentMap; % skip, same entry
      _ -> maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1)
    end
            end, VarMap, VarMap).


subsume_coclauses(Pv, Nv, T, VarMap) ->
   maps:fold(fun({Pv1, Nv1}, T1, CurrentMap) ->
    case {Pv1, Nv1, T1} of
      {Pv, Nv, T} -> CurrentMap; % skip, same entry
      _ -> maybe_remove_subsumed_coclauses(CurrentMap, {Pv, Nv, T}, {Pv1, Nv1, T1})
    end
             end, VarMap, VarMap).

maybe_remove_subsumed_coclauses(CurrentMap, _CurrentCoclause = {Pv, Nv, T}, _OtherCoclause = {Pv1, Nv1, T1}) ->
  S = fun(E) -> sets:from_list(E) end,
  % other variables in current variables
  % other neg variables in current neg variables
  % other ty in current ty
  % => remove other coclause
%%  io:format(user,"Check current~n~p~n against other ~n~p~n", [{Pv, Nv, T}, {Pv1, Nv1, T1}]),
  case sets:is_subset(S(Pv), S(Pv1)) andalso sets:is_subset(S(Nv), S(Nv1)) andalso ty_rec:is_subtype(T1, T) of
    true ->
%%      io:format(user, "Removing~n~p~n because ~n~p~n is bigger from current map: ~p~n", [{Pv1, Nv1, T1}, {Pv, Nv, T}, CurrentMap]),
      maps:remove({Pv1, Nv1}, CurrentMap);
    _ ->
      CurrentMap
  end.


maybe_remove_redundant_negative_variables(CurrentMap, T1, T, [], Nv, Pv1, Nv1) -> CurrentMap;
maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1) ->
  S = fun(E) -> sets:from_list(E) end,
  % if other dnf is subtype of current dnf,
  % remove all other negative variables that are in the current positive variables
%%  io:format(user,"Clause ~p~n", [{Pv, Nv, T}]),
%%  io:format(user,"Other Clause ~p~n", [{Pv1, Nv1, T1}]),
%%  io:format(user,"Check~n~p <: ~p~n~p in ~p~n~p in ~p~n", [T1, T, Pv, Nv1, Nv, Nv1]),
  case
    ty_rec:is_equivalent(T1, T)
      andalso sets:is_subset(S(Pv), S(Nv1)) % removeable variables
      andalso sets:is_subset(S(Nv), S(Nv1 -- Pv))
  of
    true ->
      NewMap = maps:remove({Pv1, Nv1}, CurrentMap),
      NewKey = {Pv1, Nv1 -- Pv},
      OldValue = maps:get(NewKey, CurrentMap, ty_rec:empty()),
      NewValue = ty_rec:union(OldValue, T1),
%%      io:format(user, "Removing subsumed positive variable ~p from ~n~p~nResulting in ~p~n", [Pv, {Pv1, Nv1}, NewValue]),
      maps:put(NewKey, NewValue, NewMap);
    false -> CurrentMap
  end.


multi_transform(DefaultT, T, Ops = #{any_tuple_i := Tuple, any_tuple := Tuples, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_tuple:transform(DefaultT, Ops),
  Xs = lists:map(fun({_Size, Tuple}) -> dnf_var_ty_tuple:transform(Tuple, Ops) end, maps:to_list(T)),
  Sizes = maps:keys(T),

  DefaultTuplesWithoutExplicitTuples = Intersect([X1, Tuples(), Negate(Union([Tuple(I) || I <- Sizes]))]),
  Union([DefaultTuplesWithoutExplicitTuples, Union(Xs)]).

multi_transform_fun(DefaultF, F, Ops = #{any_function_i := Function, any_function := Functions, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_function:transform(DefaultF, Ops),
  Xs = lists:map(fun({_Size, Function}) -> dnf_var_ty_function:transform(Function, Ops) end, maps:to_list(F)),
  Sizes = maps:keys(F),

  DefaultFunctionsWithoutExplicitFunctions = Intersect([X1, Functions(), Negate(Union([Function(I) || I <- Sizes]))]),
  Union([DefaultFunctionsWithoutExplicitFunctions, Union(Xs)]).


extract_variables(Ty = #ty{ predef = P, atom = A, interval = I, list = L, tuple = T, function = F }) ->
  PossibleVars = lists:foldl(fun(E, Acc) ->
    sets:intersection(sets:from_list(E), Acc)
              end, sets:from_list(dnf_var_predef:all_variables(P)),
    [
      dnf_var_ty_atom:all_variables(A),
      dnf_var_int:all_variables(I),
      dnf_var_ty_list:all_variables(L),
      dnf_var_ty_tuple:all_variables(T),
      dnf_var_ty_function:all_variables(F)
    ]),


  {Vars, NewTy} = lists:foldl(fun(Var, {ExtractedVars, TTy}) ->
    case ty_rec:is_subtype(ty_rec:variable(Var), TTy) of
      true ->
        {[Var | ExtractedVars],
        ty_rec:diff(TTy, ty_rec:variable(Var))};
      false -> {ExtractedVars, TTy}
    end
                      end, {[], ty_ref:store(Ty)}, sets:to_list(PossibleVars)),

  {Vars, NewTy}.

% ======
% Type constructors
% ======

%%rep_map_any()  -> {dnf_ty_variable:any(), #{}}.
%%rep_map_none() -> {dnf_ty_variable:empty(), #{}}.

-spec empty() -> ty_ref().
empty() ->
  ty_ref:store(#ty{
    predef = dnf_var_predef:empty(),
    atom = dnf_var_ty_atom:empty(),
    interval = dnf_var_int:empty(),
    list = dnf_var_ty_list:empty(),
    tuple = {dnf_var_ty_tuple:empty(), #{}},
    function = {dnf_var_ty_function:empty(), #{}}
  }).

-spec any() -> ty_ref().
any() ->
  ty_ref:any().

-spec variable(ty_variable()) -> ty_ref().
variable(Var) ->
  Any = ty_ref:load(any()),

  ty_ref:store(Any#ty{
    predef = dnf_var_predef:intersect(Any#ty.predef, dnf_var_predef:var(Var)),
    atom = dnf_var_ty_atom:intersect(Any#ty.atom, dnf_var_ty_atom:ty_var(Var)),
    interval = dnf_var_int:intersect(Any#ty.interval, dnf_var_int:var(Var)),
    list = dnf_var_ty_list:intersect(Any#ty.list, dnf_var_ty_list:var(Var)),
    tuple = {dnf_var_ty_tuple:var(Var), #{}},
    function ={dnf_var_ty_function:var(Var), #{}}
  }).

list() -> list(dnf_var_ty_list:any()).
list(List) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ list = List }).

-spec atom(ty_atom()) -> ty_ref().
atom(Atom) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ atom = Atom }).

-spec atom() -> ty_ref().
atom() -> atom(dnf_var_ty_atom:any()).

-spec interval(interval()) -> ty_ref().
interval(Interval) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ interval = Interval }).

-spec interval() -> ty_ref().
interval() -> interval(dnf_var_int:any()).

predef(Predef) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ predef = Predef }).
predef() -> predef(dnf_var_predef:any()).


%%-spec tuple(ty_tuple()) -> ty_ref().
tuple({default, Sizes}, Tuple) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {Tuple, NotCaptured}});
tuple(ComponentSize, Tuple) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), #{ComponentSize => Tuple}} }).

-spec tuple() -> ty_ref().
tuple() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:any(), #{}} }).

%%-spec function(ty_ref(), ty_ref()) -> ty_ref().
%%function(A, B) ->
%%  Empty = ty_ref:load(empty()),
%%  Fun = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(A, B))),
%%  ty_ref:store(Empty#ty{ function = Fun }).

function({default, Sizes}, Function) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_function:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {Function, NotCaptured}});
%%-spec function(ty_function()) -> ty_ref().
function(ComponentSize, Fun) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {dnf_var_ty_function:empty(), #{ComponentSize => Fun} }}).

-spec function() -> ty_ref().
function() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {dnf_var_ty_function:any(), #{}} }).

% ======
% Boolean operations
% ======

-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(TyRef1, TyRef2) ->
  ty_ref:op_cache(intersect, {TyRef1, TyRef2},
    fun() ->
      #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = T1, function = F1} = ty_ref:load(TyRef1),
      #ty{predef = P2, atom = A2, interval = I2, list = L2, tuple = T2, function = F2} = ty_ref:load(TyRef2),
      ty_ref:store(#ty{
        predef = dnf_var_predef:intersect(P1, P2),
        atom = dnf_var_ty_atom:intersect(A1, A2),
        interval = dnf_var_int:intersect(I1, I2),
        list = dnf_var_ty_list:intersect(L1, L2),
        tuple = multi_intersect(T1, T2),
        function = multi_intersect_fun(F1, F2)
      })
    end
    ).

-spec negate(ty_ref()) -> ty_ref().
negate(TyRef1) ->
  ty_ref:op_cache(negate, {TyRef1},
    fun() ->
      #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = {DT, T}, function = {DF, F}} = ty_ref:load(TyRef1),
      ty_ref:store(#ty{
        predef = dnf_var_predef:negate(P1),
        atom = dnf_var_ty_atom:negate(A1),
        interval = dnf_var_int:negate(I1),
        list = dnf_var_ty_list:negate(L1),
        tuple = {dnf_var_ty_tuple:negate(DT), maps:map(fun(_K,V) -> dnf_var_ty_tuple:negate(V) end, T)},
        function = {dnf_var_ty_function:negate(DF), maps:map(fun(_K,V) -> dnf_var_ty_function:negate(V) end, F)}
      })
    end).

-spec diff(ty_ref(), ty_ref()) -> ty_ref().
diff(A, B) ->
  ty_ref:op_cache(diff, {A, B},
    fun() ->
      intersect(A, negate(B))
    end).

-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(A, B) ->
  ty_ref:op_cache(union, {A, B},
    fun() ->
  negate(intersect(negate(A), negate(B)))
     end).

multi_intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_tuple:intersect(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
                 end,
  {dnf_var_ty_tuple:intersect(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

multi_intersect_fun({DefaultF1, F1}, {DefaultF2, F2}) ->
  % get all keys
  AllKeys = maps:keys(F1) ++ maps:keys(F2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_function:intersect(
      maps:get(Key, F1, DefaultF1),
      maps:get(Key, F2, DefaultF2)
    )
                 end,
  {dnf_var_ty_function:intersect(DefaultF1, DefaultF2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.


is_empty(TyRef) ->
  % first try op-cache
  case ty_ref:is_empty_cached(TyRef) of
    R when R == true; R == false -> R;
    miss ->
      ty_ref:store_is_empty_cached(TyRef, is_empty_miss(TyRef))
  end.

is_empty_miss(TyRef) ->
  Ty = ty_ref:load(TyRef),
  dnf_var_predef:is_empty(Ty#ty.predef)
  andalso dnf_var_ty_atom:is_empty(Ty#ty.atom)
    andalso dnf_var_int:is_empty(Ty#ty.interval)
    andalso (
      begin
        case ty_ref:is_empty_memoized(TyRef) of
          true ->
            true;
          miss ->
            % memoize
            ok = ty_ref:memoize(TyRef),
            dnf_var_ty_list:is_empty(Ty#ty.list)
            andalso multi_empty_tuples(Ty#ty.tuple)
              andalso multi_empty_functions(Ty#ty.function)
        end
      end
  ).

multi_empty_tuples({Default, AllTuples}) ->
  dnf_var_ty_tuple:is_empty(Default)
    andalso
  maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_tuple:is_empty(V) end, true, AllTuples).

multi_empty_functions({Default, AllFunctions}) ->
  dnf_var_ty_function:is_empty(Default)
    andalso
    maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_function:is_empty(V) end, true, AllFunctions).

is_any(_Arg0) ->
  erlang:error(any_not_implemented). % TODO needed?

normalize(TyRef, Fixed, M) ->
  case ty_ref:normalized_memoized({TyRef, Fixed}) of
    miss ->
      ty_ref:memoize_norm({TyRef, Fixed}, Sol = normalize_miss(TyRef, Fixed, M)),
      Sol;
    R -> R
  end.

normalize_miss(TyRef, Fixed, M) ->

  Ty = ty_ref:load(TyRef),
  PredefNormalize = dnf_var_predef:normalize(Ty#ty.predef, Fixed, M),
  AtomNormalize = dnf_var_ty_atom:normalize(Ty#ty.atom, Fixed, M),
  Both = constraint_set:merge_and_meet(PredefNormalize, AtomNormalize),
  case Both of
    [] -> [];
    _ ->

      IntervalNormalize = dnf_var_int:normalize(Ty#ty.interval, Fixed, M),
      Res1 = constraint_set:merge_and_meet(Both, IntervalNormalize),
      case Res1 of
        [] -> [];
        _ ->
          begin
                Res2 = multi_normalize_tuples(Ty#ty.tuple, Fixed, M),
                ResX = fun() -> constraint_set:merge_and_meet(Res1, Res2) end,
                ResLists = fun() -> dnf_var_ty_list:normalize(Ty#ty.list, Fixed, M) end,
                Res3 = constraint_set:meet(ResX, ResLists),
                case Res3 of
                  [] -> [];
                  _ ->
                    Res4 = multi_normalize_functions(Ty#ty.function, Fixed, M),
                    constraint_set:merge_and_meet(Res3, Res4)
                end
          end
      end
  end.

multi_normalize_tuples({Default, AllTuples}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_tuple:normalize(Size, V, Fixed, M))
      )
              end, [[]], AllTuples)
  ),

  DF = ?F(dnf_var_ty_tuple:normalize({default, maps:keys(AllTuples)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

multi_normalize_functions({Default, AllFunctions}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_function:normalize(Size, V, Fixed, M))
      )
              end, [[]], AllFunctions)
  ),

  DF = ?F(dnf_var_ty_function:normalize({default, maps:keys(AllFunctions)}, Default, Fixed, M)),

  constraint_set:meet(
    DF,
    Others
  ).

substitute(TyRef, SubstituteMap) ->
  % the left map is the current projection
  % the right map is the original substitution map
  substitute(TyRef, SubstituteMap, #{}).

% var => ty_rec
% once the map arrives here, is should be the same again
substitute(TyRef, SubstituteMap, OldMemo) ->
%%  io:format(user, "Doing a substitution with ~p and map ~p~n", [ty_ref:load(TyRef), SubstituteMap]),
  case maps:get(TyRef, OldMemo, undefined) of
    undefined ->
      Ty = #ty{
        predef = Predef,
        atom = Atoms,
        interval = Ints,
        list = Lists,
        tuple = {DefaultT, AllTuples},
        function = {DefaultF, AllFunctions}
      } = ty_ref:load(TyRef),


      case has_ref(Ty, TyRef) of
        true ->
          RecursiveNewRef = ty_ref:new_ty_ref(),
          Memo = OldMemo#{TyRef => RecursiveNewRef},
          NewTy = #ty{
            predef = dnf_var_predef:substitute(fun(TTy) -> pi(predef, TTy) end, Predef, SubstituteMap, Memo),
            atom = dnf_var_ty_atom:substitute(fun(TTy) -> pi(atom, TTy) end,Atoms, SubstituteMap, Memo),
            interval = dnf_var_int:substitute(fun(TTy) -> pi(interval, TTy) end, Ints, SubstituteMap, Memo),
            list = dnf_var_ty_list:substitute(fun(TTy) -> pi(list, TTy) end, Lists, SubstituteMap, Memo),
            tuple = multi_substitute(DefaultT, AllTuples, SubstituteMap, Memo),
            function = multi_substitute_fun(DefaultF, AllFunctions, SubstituteMap, Memo)
          },
          ty_ref:define_ty_ref(RecursiveNewRef, NewTy);
        false ->
          NewTy = #ty{
            predef = dnf_var_predef:substitute(fun(TTy) -> pi(predef, TTy) end, Predef, SubstituteMap, OldMemo),
            atom = dnf_var_ty_atom:substitute(fun(TTy) -> pi(atom, TTy) end, Atoms, SubstituteMap, OldMemo),
            interval = dnf_var_int:substitute(fun(TTy) -> pi(interval, TTy) end, Ints, SubstituteMap, OldMemo),
            list = dnf_var_ty_list:substitute(fun(TTy) -> pi(list, TTy) end, Lists, SubstituteMap, OldMemo),
            tuple = multi_substitute(DefaultT, AllTuples, SubstituteMap, OldMemo),
            function = multi_substitute_fun(DefaultF, AllFunctions, SubstituteMap, OldMemo)
          },
%%          io:format(user, "Substitute ~p to ~p~nGot ~p~n", [Ty, SubstituteMap, NewTy]),
          ty_ref:store(NewTy)
      end;

    ToReplace -> ToReplace
  end.

tuple_keys(TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_T, Map} = Ty#ty.tuple,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).

function_keys(TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_T, Map} = Ty#ty.function,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).


multi_substitute(DefaultTuple, AllTuples, SubstituteMap, Memo) ->
  % substitute default tuple, get a new default tuple
%%  io:format(user, "From default: ~p~n", [DefaultTuple]),
  NewDefaultTuple = dnf_var_ty_tuple:substitute( fun(Ty) -> pi({tuple, default}, Ty) end, DefaultTuple, SubstituteMap, Memo),
%%  io:format(user, "Into new default: ~p~n", [NewDefaultTuple]),

  % the default tuple can be substituted to contain other explicit tuple lengths
  % example: {alpha, 0} with alpha := {1,1} ==> {0, 2 -> {1,1}}
  % projecting just the default tuple value 0 loses information
  % we need to get these explicit tuple lengths out of the substituted default tuple:
  % get all lengths after substitution,
  % and substitute the default tuple for each length,
  % filtering with the appropriate length projection function
  AllVars = dnf_var_ty_tuple:all_variables(DefaultTuple),
  % note: OtherTupleKeys not be included in the AllTuples keys, they are known
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> tuple_keys(V) -- maps:keys(AllTuples) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
%%  Keys = [(tuple_keys(V) -- maps:keys(AllTuples)) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherTupleKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherTuples = maps:from_list([{Length, dnf_var_ty_tuple:substitute( fun(Ty) -> pi({tuple, Length}, Ty) end, DefaultTuple, SubstituteMap, Memo)} || Length <- OtherTupleKeys]),

  % all explicit keys are now all defined tuples and all newly explicit tuples after default substitution
  AllKeys = maps:keys(AllTuples) ++ maps:keys(NewDefaultOtherTuples),

  % TODO the above can happen with explicit tuples, introducing new explicit tuples not known before
  % TODO test case:
  % {0, 2 => alpha} with alpha := {1,1,1} ==> {0, 3 => {1,1,1}}
  % for explicit tuples, collect all other lengths into a new map, yielding a list of maps
  % merge (union) these maps into NewOtherTuples
  NewOtherTuples = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllTuples) of
            true ->
              OtherFixedTuples = maps:from_list([
                {Length, dnf_var_ty_tuple:substitute( fun(Ty) -> pi({tuple, Length}, Ty) end, maps:get(Key, AllTuples), SubstituteMap, Memo)} || Length <- OtherTupleKeys
              ]),
              case length(maps:keys(OtherFixedTuples)) > 0 of true ->
                io:format(user, "Doing a substitution with this tuple: ~p~n", [{DefaultTuple, AllTuples}]),
                io:format(user, "With the map: ~p~n", [SubstituteMap]),
                io:format(user, "Creates new tuples!: ~p~n", [OtherFixedTuples]),
                error({todo, othertuples, OtherFixedTuples});
                false -> ok end,
%%              io:format(user, "Substitute ~p with ~p~n", [maps:get(Key, AllTuples), SubstituteMap]),
              E = dnf_var_ty_tuple:substitute( fun(Ty) ->
%%                io:format(user, "Got ~p~n All Tuples: ~p~n", [ty_ref:load(Ty), AllTuples]),
                pi({tuple, Key}, Ty)
                                           end, maps:get(Key, AllTuples), SubstituteMap, Memo),
%%              io:format(user, "DONE~n", []),
              E
            ;
            _ -> maps:get(Key, NewDefaultOtherTuples, NewDefaultTuple)
          end}
                                            end, AllKeys)),

  {NewDefaultTuple, NewOtherTuples}.

multi_substitute_fun(DefaultFunction, AllFunctions, SubstituteMap, Memo) ->
  % see multi_substitute for comments
  % TODO refactor abstract into one function for both tuples and funcions
  NewDefaultFunction = dnf_var_ty_function:substitute( fun(Ty) -> pi({function, default}, Ty) end, DefaultFunction, SubstituteMap, Memo),
  AllVars = dnf_var_ty_tuple:all_variables(DefaultFunction),
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> function_keys(V) -- maps:keys(AllFunctions) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
%%  Keys = [function_keys(V) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherFunctionKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherFunctions = maps:from_list([{Length, dnf_var_ty_function:substitute( fun(Ty) -> pi({function, Length}, Ty) end, DefaultFunction, SubstituteMap, Memo)} || Length <- OtherFunctionKeys]),
  AllKeys = maps:keys(AllFunctions) ++ maps:keys(NewDefaultOtherFunctions),

  % TODO FIXME same problem as tuples, see multi_substitute
  NewOtherFunctions = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllFunctions) of
            true ->
              OtherFixedFunctions = maps:from_list([
                {Length, dnf_var_ty_function:substitute( fun(Ty) -> pi({function, Length}, Ty) end, maps:get(Key, AllFunctions), SubstituteMap, Memo)} || Length <- OtherFunctionKeys
              ]),
              case length(maps:keys(OtherFixedFunctions)) > 0 of true -> error({todo, otherfunctions, OtherFixedFunctions}); false -> ok end,
              dnf_var_ty_function:substitute( fun(Ty) -> pi({function, Key}, Ty) end, maps:get(Key, AllFunctions), SubstituteMap, Memo) ;
            _ -> maps:get(Key, NewDefaultOtherFunctions, NewDefaultFunction)
          end}
                                            end, AllKeys)),

  {NewDefaultFunction, NewOtherFunctions}.

has_ref(#ty{list = Lists, tuple = {Default, AllTuple}, function = {DefaultF, AllFunction}}, TyRef) ->
  % TODO sanity remove
  false = dnf_var_ty_tuple:has_ref(Default, TyRef), % should never happen
  false = dnf_var_ty_function:has_ref(DefaultF, TyRef), % should never happen
  dnf_var_ty_list:has_ref(Lists, TyRef)
  orelse
  maps:fold(fun(_K,T, All) -> All orelse dnf_var_ty_tuple:has_ref(T, TyRef) end, false, AllTuple)
  orelse
  maps:fold(fun(_K,F, All) -> All orelse dnf_var_ty_function:has_ref(F, TyRef) end, false, AllFunction).

pi(atom, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.atom;
pi(interval, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.interval;
pi(list, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.list;
pi(tuple, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.tuple;
pi({tuple, default}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {D, _TM} = Ty#ty.tuple,
  D;
pi({tuple, Len}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {D, TM} = Ty#ty.tuple,
  maps:get(Len, TM, D);
pi({function, default}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {D, _TM} = Ty#ty.function,
  D;
pi({function, Len}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {D, TM} = Ty#ty.function,
  maps:get(Len, TM, D);
pi(predef, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.predef;
pi(function, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.function.

all_variables(TyRef) ->
  #ty{
    predef = Predefs,
    atom = Atoms,
    interval = Ints,
    list = Lists,
    tuple = Tuples,
    function = Functions
  } = ty_ref:load(TyRef),


  lists:usort(
    dnf_var_predef:all_variables(Predefs)
  ++  dnf_var_ty_atom:all_variables(Atoms)
  ++ dnf_var_int:all_variables(Ints)
  ++ dnf_var_ty_list:all_variables(Lists)
  ++ dnf_var_ty_tuple:all_variables(Tuples)
  ++ dnf_var_ty_function:all_variables(Functions)).

%%-ifdef(TEST).
%%-include_lib("eunit/include/eunit.hrl").
%%
%%usage_test() ->
%%  Lists = ty_ref:new_ty_ref(),
%%  ListsBasic = ty_ref:new_ty_ref(),
%%
%%  % nil
%%  Nil = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([nil]))),
%%
%%  % (alpha, Lists)
%%  Alpha = ty_variable:new("alpha"),
%%  AlphaTy = ty_rec:variable(Alpha),
%%  Tuple = ty_rec:tuple(dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([AlphaTy, Lists])))),
%%  Recursive = ty_rec:union(Nil, Tuple),
%%
%%  ty_ref:define_ty_ref(Lists, ty_ref:load(Recursive)),
%%
%%  SomeBasic = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([somebasic]))),
%%  SubstMap = #{Alpha => SomeBasic},
%%  Res = ty_rec:substitute(Lists, SubstMap),
%%
%%  Tuple2 = ty_rec:tuple(dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([SomeBasic, ListsBasic])))),
%%  Expected = ty_rec:union(Nil, Tuple2),
%%  ty_ref:define_ty_ref(ListsBasic, ty_ref:load(Expected)),
%%
%%  true = ty_rec:is_equivalent(Res, Expected),
%%
%%  ok.
%%
%%-endif.
