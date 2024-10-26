-module(ty_rec).

-define(debug, true).

-include_lib("sanity.hrl").

-define(F(Z), fun() -> Z end).


-export([has_ref/2, equal/2, empty/0, any/0]).
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

-export([transform/2, print/1, unwrap_tuple/2, compare/2]).

-record(ty, {predef, atom, interval, list, tuple, function}).

-type ty_ref() :: {ty_ref, integer()}.
-type interval() :: term().
%%-type ty_tuple() :: term().
%%-type ty_function() :: term().
-type ty_variable() :: term().
-type ty_atom() :: term().

equal(X, Y) -> X =:= Y.
% dummy not needed
compare(X, X) -> 0;
compare(X, Y) -> case X < Y of true -> -1; _ -> 1 end.

unwrap_tuple(RRef, Dim) ->
  Unwrap = fun(_Index, AllTuples ) -> 
    Multi = lists:map(fun({Components, Ref}) -> 
      case ty_ref:load(Ref) of
        #ty{ tuple = {_, _, _, #{2 := T}} } ->
          {terminal, Tuples} = T,

          AllR = lists:map(fun(Tup) -> 
            A = ty_tuple:pi(1, Tup),
            B = ty_tuple:pi(2, Tup),
            {Components ++ [A], B}
          end, Tuples),

          AllR;
        % special case s
        % Any -> (Any, Any) unfold
        % TODO Empty -> (Empty, Empty) unfold possible?
        #ty{ tuple = {{terminal, top_2tuple}, _, _, _} } ->
          A = ty_rec:any(),
          B = ty_rec:any(),
          [{Components ++ [A], B}]
      end
    end, AllTuples),
    lists:flatten(Multi)
  end,

  All = lists:foldl(Unwrap, [{[], RRef}], lists:seq(2, Dim)),
  lists:map(fun({Comps, Last}) -> Comps ++ [Last] end, All).

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
    false -> 
      case subty:is_subty(symtab:empty(), Other, Z2) of %TODO symtab?
        true -> Other;
        false -> 
          Intersect([Other, Z2])
      end
  end.

transform(TyRef, Ops) ->
  {Pol, Full} = stransform(TyRef, Ops),
  case Pol of
      pos -> Full;
      neg -> stdtypes:tnegate(Full)
  end.

stransform(TyRef, Ops) ->
  % Do things twice, pos and neg
  Pos = transform_p(TyRef, Ops),
  Neg = transform_p(ty_rec:negate(TyRef), Ops),

  % very dumb heuristic: smaller is better
  case
    size(term_to_binary(Pos)) > size(term_to_binary(Neg))
  of
    false -> {pos, Pos};
    _ ->
      % fix1: any is smaller than none, pick none anyway
      case stdtypes:tnone() of
        Pos -> {pos, Pos};
        _ -> {neg, Neg}
      end
  end.

transform_p({ty_ref, 0}, #{any := Any}) -> Any();
transform_p({ty_ref, 1}, #{empty := Empty}) -> Empty();
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
  % io:format(user,"<~p> Transforming: ~p~n~p~n", [Ref = make_ref(), TyRef, ty_ref:load(TyRef)]),
  DnfMap = prepare(TyRef),
%%  io:format(user, "<~p> Prepared: ~n~p~n", [Ref, DnfMap]),

  Mapped = maps:map(fun({Pv, Nv}, TyR) ->
    NewVars = lists:map(fun(K) -> Var(K) end, Pv),
    NewVarsN = lists:map(fun(K) -> Negate(Var(K)) end, Nv),
    case ty_rec:is_subtype(ty_rec:any(), TyR) of
      true ->
        Intersect(NewVars ++ NewVarsN);
      _ ->
        #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T0, T1, Tn}, function = {DF, F}} = ty_ref:load(TyR),
        NP = maybe_intersect(dnf_var_predef:transform(P, Ops), Predef(), Intersect),
        NA = maybe_intersect(dnf_var_ty_atom:transform(A, Ops), Atoms(), Intersect),
        NI = maybe_intersect(dnf_var_int:transform(I, Ops), Intervals(), Intersect),
        NL = maybe_intersect(dnf_var_ty_list:transform(L, Ops), Lists(), Intersect),

        Z1 = multi_transform(DT, T0, T1, Tn, Ops),
        NT = maybe_intersect(Z1, Tuples(), Intersect),

        Z2 = multi_transform_fun(DF, F, Ops),
        NF = maybe_intersect(Z2, Functions(), Intersect),
        Intersect(NewVars ++ NewVarsN ++ [Union([NP, NA, NI, NL, NT, NF])])
    end
           end, DnfMap),

  Ety = Union(maps:values(Mapped)),
  Sanity = ast_lib:ast_to_erlang_ty(Ety),
  % io:format(user,"<~p> Sanity: ~p~n", [Ety, Sanity]),
  % leave this sanity check for a while
  case is_equivalent(TyRef, Sanity) of
    true -> ok;
    false ->
      io:format(user, "--------~n", []),
      io:format(user, "~p~n", [TyRef]),
      io:format(user, "~p~n", [ty_ref:load(TyRef)]),
      io:format(user, "~p~n", [Ety]),
      io:format(user, "~p~n", [ty_ref:load(Sanity)]),
      error(todo)
  end,
  Ety.

% TODO refactor this properly it's ugly
prepare(TyRef) ->
  #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T0, T1, Tn}, function = {DF, F}} = ty_ref:load(TyRef),
  VarMap = #{},

  PDnf = dnf_var_predef:get_dnf(P),
  ADnf = dnf_var_ty_atom:get_dnf(A),
  IDnf = dnf_var_int:get_dnf(I),
  LDnf = dnf_var_ty_list:get_dnf(L),

  PMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:predef(dnf_var_predef:predef(Ty))} end, PDnf),
  AMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:atom(dnf_var_ty_atom:ty_atom(Ty))} end, ADnf),
  IMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:interval(dnf_var_int:int(Ty))} end, IDnf),
  LMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:list(dnf_var_ty_list:list(Ty))} end, LDnf),


  TupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple({default, maps:keys(Tn)}, dnf_var_ty_tuple:tuple(Tp))} end, dnf_var_ty_tuple:get_dnf(DT)),
  Tuple0Mapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple(0, dnf_var_ty_bool:bool(Tp))} end, dnf_var_ty_bool:get_dnf(T0)),
  Tuple1Mapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple(1, dnf_var_ty_ref:ref(Tp))} end, dnf_var_ty_ref:get_dnf(T1)),
  TupleExplicitMapped = lists:flatten(lists:map(fun({Size, Tuple}) ->
    DnfTuples = dnf_var_ty_tuple:get_dnf(Tuple),
    _DnfTupleMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:tuple(Size, dnf_var_ty_tuple:tuple(Tp))} end, DnfTuples)
                                  end, maps:to_list(Tn))),

  FunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function({default, maps:keys(F)}, dnf_var_ty_function:function(Tp))} end, dnf_var_ty_function:get_dnf(DF)),
  FunctionExplicitMapped = lists:map(fun({Size, Function}) ->
    DnfFunctions = dnf_var_ty_function:get_dnf(Function),
    _DnfFunctionMapped = lists:map(fun({Pv, Nv, Tp}) -> {{Pv, Nv}, ty_rec:function(Size, dnf_var_ty_function:function(Tp))} end, DnfFunctions)
                                     end, maps:to_list(F)),

  AllKinds = lists:flatten([PMapped, AMapped, IMapped, LMapped, TupleMapped, FunctionMapped, Tuple0Mapped, Tuple1Mapped, TupleExplicitMapped, FunctionExplicitMapped]),

  UpdateKey = fun(_Key, Ty1, Ty2) -> ty_rec:union(Ty1, Ty2) end,
  AllUnions = lists:foldl(fun({VarKey, Ty}, CurrentMap) ->
    NewMap = #{VarKey => Ty},
    maps:merge_with(UpdateKey, CurrentMap, NewMap)
                          end, VarMap, AllKinds),

%%  io:format(user,"All unions;~n~p~n", [AllUnions]),
  Phase1 = fun Loop(Map) ->
    Res = catch maps:fold(fun({Pv, Nv}, Ty, CurrentMap) -> subsume_variables(Pv, Nv, Ty, CurrentMap) end, Map, Map),
    case Res of
      {modified, NewMap} -> Loop(NewMap);
      _ -> Res
    end
           end,
  SubsumedUnions1 = Phase1(AllUnions),

  % TODO repeat phase2 like phase1
  SubsumedUnions2 = maps:fold(fun({Pv, Nv}, Ty, CurrentMap) ->
    subsume_coclauses(Pv, Nv, Ty, CurrentMap)
                             end, SubsumedUnions1, SubsumedUnions1),

%%  io:format(user, "All: ~n~p~n", [AllUnions]),
%%  io:format(user, "Subsumed: ~n~p~n", [SubsumedUnions]),
%%  io:format(user, "Subsumed all: ~n~p~n", [SubsumedUnions2]),

  % Distribute top types to all variables redundantly, if any
  % atom() | a & (Any \ atom) => atom() | a
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
      {Pv, Nv, T} ->
        CurrentMap; % skip, same entry
      _ ->
        maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1)
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


maybe_remove_redundant_negative_variables(CurrentMap, T1, T, Pv, Nv, Pv1, Nv1) ->
  S = fun(E) -> sets:from_list(E) end,
  % if other dnf is subtype of current dnf,
  % remove all other negative variables that are in the current positive variables
%%  io:format(user,"Clause ~p~n", [{Pv, Nv, T}]),
%%  io:format(user,"Other Clause ~p~n", [{Pv1, Nv1, T1}]),
%%  io:format(user,"Check~n~p <: ~p~n~p in ~p~n~p in ~p~n", [T1, T, Pv, Nv1, Nv, Nv1]),
  case
    ty_rec:is_subtype(T1, T)
      andalso sets:is_subset(S(Pv), S(Nv1))
      andalso sets:is_subset(S(Nv), S(Nv1 -- Pv))
      andalso sets:is_subset(S(Pv1), S(Pv))
  of
    true ->
      NewMap = maps:remove({Pv1, Nv1}, CurrentMap),
      NewKey = {Pv1, Nv1 -- Pv},
      OldValue = maps:get(NewKey, CurrentMap, ty_rec:empty()),
      NewValue = ty_rec:union(OldValue, T1),
%%      io:format(user, "Removing subsumed positive variable ~p from ~n~p~nResulting in ~p~n", [Pv, {Pv1, Nv1}, NewValue]),
      NewNewMap = maps:put(NewKey, NewValue, NewMap),
      % FIXME skip this case instead
      case NewNewMap == CurrentMap of
        true -> NewNewMap;
        _ -> throw({modified, NewNewMap})
      end;
    false ->
      case
        ty_rec:is_equivalent(T1, T)
          andalso sets:is_subset(S(Pv), S([]))
          andalso Pv1 == Nv
      of
        true ->
          NewMap = maps:remove({Pv1, Nv1}, CurrentMap),
          NewKey = {Pv1 -- Nv, Nv1},
          OldValue = maps:get(NewKey, CurrentMap, ty_rec:empty()),
          NewValue = ty_rec:union(OldValue, T1),
          NewNewMap = maps:put(NewKey, NewValue, NewMap),
          % FIXME skip this case instead
          case NewNewMap == CurrentMap of
            true -> NewNewMap;
            _ -> throw({modified, NewNewMap})
          end;
        false ->
          CurrentMap
      end
  end.


multi_transform(DefaultT, T0, T1, Tn, Ops = #{any_tuple_i := Tuple, any_tuple := Tuples, negate := Negate, union := Union, intersect := Intersect}) ->
  Xd = dnf_var_ty_tuple:transform(DefaultT, Ops),
  X0 = maybe_intersect(dnf_var_ty_bool:transform(T0, Ops#{any => fun() -> Tuple(0) end }), Tuple(0), Intersect),
  X1 = maybe_intersect(dnf_var_ty_ref:transform(T1, Ops#{any => fun() -> Tuple(1) end }), Tuple(1), Intersect),
  Xs = lists:map(fun
    ({Size, Tup}) when Size > 2 -> 
      R = dnf_var_ty_tuple:transform(Tup, Ops#{tuple_dim => Size}),
      maybe_intersect(R, Tuple(Size), Intersect);
    ({2, Tup}) ->
    % if a tuple is semantically equivalent to empty, return empty instead of the empty tuple
    case dnf_var_ty_tuple:is_empty(Tup) of
      true -> dnf_var_ty_tuple:transform(dnf_var_ty_tuple:empty(), Ops);
      _ -> 
        R = dnf_var_ty_tuple:transform(Tup, Ops),
        % just transforming resulst in {predef, any} which is wrong
        maybe_intersect(R, Tuple(2), Intersect)
    end
                 end, maps:to_list(Tn)),
  Sizes = maps:keys(Tn),

  % io:format(user, "Default: ~p~n", [DefaultT]),
  % io:format(user, "T0: ~p~n", [T0]),
  % io:format(user, "T1: ~p~n", [T1]),
  % io:format(user, "Tn: ~p~n", [Tn]),
  DefaultTuplesWithoutExplicitTuples = Intersect([Xd, Tuples(), Negate(Union([Tuple(0), Tuple(1)] ++ [Tuple(I) || I <- Sizes]))]),
  R = Union([DefaultTuplesWithoutExplicitTuples, Union([X0, X1] ++ Xs)]),
  R.

multi_transform_fun(DefaultF, F, Ops = #{any_function_i := Function, any_function := Functions, negate := Negate, union := Union, intersect := Intersect}) ->
  X1 = dnf_var_ty_function:transform(DefaultF, Ops),
  Xs = lists:map(fun({_Size, Func}) -> dnf_var_ty_function:transform(Func, Ops) end, maps:to_list(F)),
  Sizes = maps:keys(F),

  DefaultFunctionsWithoutExplicitFunctions = Intersect([X1, Functions(), Negate(Union([Function(I) || I <- Sizes]))]),
  Union([DefaultFunctionsWithoutExplicitFunctions, Union(Xs)]).


extract_variables(Ty = #ty{ predef = P, atom = A, interval = I, list = L, tuple = Tall, function = F }) ->
  PossibleVars = lists:foldl(fun(E, Acc) ->
    sets:intersection(sets:from_list(E), Acc)
              end, sets:from_list(dnf_var_predef:all_variables(P)),
    [
      dnf_var_ty_atom:all_variables(A),
      dnf_var_int:all_variables(I),
      dnf_var_ty_list:all_variables(L),
      dnf_var_ty_tuple:mall_variables(Tall),
      dnf_var_ty_function:mall_variables(F)
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

-spec empty() -> ty_ref().
empty() ->
  ty_ref:empty().

-spec any() -> ty_ref().
any() ->
  ty_ref:any().

-spec variable(ty_variable()) -> ty_ref().
variable(Var) ->
  Any = ty_ref:load(any()),

  ty_ref:store(Any#ty{
    predef = dnf_var_predef:intersect(Any#ty.predef, dnf_var_predef:var(Var)),
    atom = dnf_var_ty_atom:intersect(Any#ty.atom, dnf_var_ty_atom:var(Var)),
    interval = dnf_var_int:intersect(Any#ty.interval, dnf_var_int:var(Var)),
    list = dnf_var_ty_list:intersect(Any#ty.list, dnf_var_ty_list:var(Var)),
    tuple = {dnf_var_ty_tuple:var(Var), dnf_var_ty_bool:var(Var), dnf_var_ty_ref:var(Var), #{}},
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

tuple({default, Sizes}, Tuple) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {Tuple, dnf_var_ty_bool:empty(), dnf_var_ty_ref:ref(empty()), NotCaptured}});
tuple(0, Tuple) -> 
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), Tuple, dnf_var_ty_ref:ref(empty()), #{}}});
tuple(1, Tuple) -> 
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), dnf_var_ty_bool:empty(), Tuple, #{}}});
tuple(ComponentSize, Tuple) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), dnf_var_ty_bool:empty(), dnf_var_ty_ref:ref(empty()), #{ComponentSize => Tuple}} }).
% tuple(ComponentSize, Tuple) ->
%   {terminal, _} = Tuple, % should be var dnf tuple
%   Empty = ty_ref:load(empty()),
%   ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), #{ComponentSize => Tuple}} }).
% 
set_tuple(ComponentSize, Tuple) ->
  {dnf_var_ty_tuple:empty(), dnf_var_ty_bool:empty(), dnf_var_ty_ref:ref(empty()), #{ComponentSize => Tuple}}.

-spec tuple() -> ty_ref().
tuple() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:any(), dnf_var_ty_bool:any(), dnf_var_ty_ref:any(), #{}} }).

function({default, Sizes}, Function) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_function:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {Function, NotCaptured}});
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
negate({ty_ref, 0}) -> {ty_ref, 1};
negate({ty_ref, 1}) -> {ty_ref, 0};
negate(TyRef1) ->
  ty_ref:op_cache(negate, {TyRef1},
    fun() ->
      #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = {DT, T0, T1, Tn}, function = {DF, F}} = ty_ref:load(TyRef1),
      ty_ref:store(#ty{
        predef = dnf_var_predef:negate(P1),
        atom = dnf_var_ty_atom:negate(A1),
        interval = dnf_var_int:negate(I1),
        list = dnf_var_ty_list:negate(L1),
        tuple = {dnf_var_ty_tuple:negate(DT), dnf_var_ty_bool:negate(T0), dnf_var_ty_ref:negate(T1), maps:map(fun(_K,V) -> dnf_var_ty_tuple:negate(V) end, Tn)},
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

multi_intersect({DefaultT1, T0a, T1a, T1}, {DefaultT2, T0b, T1b, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    dnf_var_ty_tuple:intersect(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
                 end,
  {dnf_var_ty_tuple:intersect(DefaultT1, DefaultT2), 
    dnf_var_ty_bool:intersect(T0a, T0b),
    dnf_var_ty_ref:intersect(T1a, T1b),
    maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

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

multi_empty_tuples({Default, T0, T1, AllTuples}) ->
  dnf_var_ty_tuple:is_empty(Default)
    andalso dnf_var_ty_bool:is_empty(T0)
    andalso dnf_var_ty_ref:is_empty(T1)
    andalso maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_tuple:is_empty(V) end, true, AllTuples).

multi_empty_functions({Default, AllFunctions}) ->
  dnf_var_ty_function:is_empty(Default)
    andalso
    maps:fold(fun(_Size, V, Acc) -> Acc andalso dnf_var_ty_function:is_empty(V) end, true, AllFunctions).

is_any(_Arg0) ->
  erlang:error(any_not_implemented). % TODO needed?

% need explicit because dnf_var_ty_ref usage
% memoization up to Fixed variables only
normalize({ty_ref, 0}, _Fixed, _M) -> [];
normalize({ty_ref, 1}, _Fixed, _M) -> [[]];
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

multi_normalize_tuples({Default, T0, T1, AllTuples}, Fixed, M) ->
  Others = ?F(
    maps:fold(fun(Size, V, Acc) ->
      constraint_set:meet(
        ?F(Acc),
        ?F(dnf_var_ty_tuple:normalize(Size, V, Fixed, M))
      )
              end, [[]], AllTuples)
  ),

  DF = ?F(dnf_var_ty_tuple:normalize({default, maps:keys(AllTuples)}, Default, Fixed, M)),
  D0 = ?F(dnf_var_ty_bool:normalize(T0, Fixed, M)),
  D1 = ?F(dnf_var_ty_ref:normalize(T1, Fixed, M)),
  DD = ?F(constraint_set:meet(D0, D1)),

  constraint_set:meet(DD, ?F(
    constraint_set:meet(
      DF,
      Others
  ))).

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
  ?TIME(substitute, substitute(TyRef, SubstituteMap, #{})).

% var => ty_rec
% once the map arrives here, is should be the same again
substitute(T = {ty_ref, 0}, _, _) -> T;
substitute(T = {ty_ref, 1}, _, _) -> T;
substitute(TyRef, SubstituteMap, OldMemo) ->
%%  io:format(user, "Doing a substitution with ~p and map ~p~n", [ty_ref:load(TyRef), SubstituteMap]),
  case maps:get(TyRef, OldMemo, undefined) of
    undefined ->
      Ty = #ty{
        predef = Predef,
        atom = Atoms,
        interval = Ints,
        list = Lists,
        tuple = {DefaultT, T0, T1, AllTuples},
        function = {DefaultF, AllFunctions}
      } = ty_ref:load(TyRef),


      case has_ref(Ty, TyRef) of
        true ->
          RecursiveNewRef = ty_ref:new_ty_ref(),
          Memo = OldMemo#{TyRef => RecursiveNewRef},
          NewTy = #ty{
            predef = ?TIME(vardef, dnf_var_predef:substitute(Predef, SubstituteMap, Memo, fun(TTy) -> pi(predef, TTy) end)),
            atom = ?TIME(atom, dnf_var_ty_atom:substitute(Atoms, SubstituteMap, Memo, fun(TTy) -> pi(atom, TTy) end)),
            interval = ?TIME(int, dnf_var_int:substitute(Ints, SubstituteMap, Memo, fun(TTy) -> pi(interval, TTy) end)),
            list = ?TIME(list, dnf_var_ty_list:substitute(Lists, SubstituteMap, Memo, fun(TTy) -> pi(list, TTy) end)),
            tuple = ?TIME(multi_tuple, multi_substitute(DefaultT, T0, T1, AllTuples, SubstituteMap, Memo)),
            function = ?TIME(multi_fun, multi_substitute_fun(DefaultF, AllFunctions, SubstituteMap, Memo))
          },
          ty_ref:define_ty_ref(RecursiveNewRef, NewTy);
        false ->
          NewTy = #ty{
            predef = ?TIME(vardef, dnf_var_predef:substitute(Predef, SubstituteMap, OldMemo, fun(TTy) -> pi(predef, TTy) end)),
            atom = ?TIME(atom, dnf_var_ty_atom:substitute(Atoms, SubstituteMap, OldMemo, fun(TTy) -> pi(atom, TTy) end)),
            interval = ?TIME(int, dnf_var_int:substitute(Ints, SubstituteMap, OldMemo, fun(TTy) -> pi(interval, TTy) end)),
            list = ?TIME(list, dnf_var_ty_list:substitute(Lists, SubstituteMap, OldMemo, fun(TTy) -> pi(list, TTy) end)),
            tuple = ?TIME(multi_tuple, multi_substitute(DefaultT, T0, T1, AllTuples, SubstituteMap, OldMemo)),
            function = ?TIME(multi_fun, multi_substitute_fun(DefaultF, AllFunctions, SubstituteMap, OldMemo))
          },
%%          io:format(user, "Substitute ~p to ~p~nGot ~p~n", [Ty, SubstituteMap, NewTy]),
          ty_ref:store(NewTy)
      end;

    ToReplace -> ToReplace
  end.

tuple_keys(TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_T, _, _, Map} = Ty#ty.tuple,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).

function_keys(TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_T, Map} = Ty#ty.function,
  maps:fold(fun(K,_,AccIn) -> [K | AccIn] end, [], Map).

multi_substitute(DefaultTuple, T0, T1, Tn, SubstituteMap, Memo) ->
  % substitute default tuple, get a new default tuple
%%  NewDefaultTuple = dnf_var_ty_tuple:csubstitute( fun(Ty) -> pi({tuple, default}, Ty) end, {tuple, default}, DefaultTuple, SubstituteMap, Memo),
  NewDefaultTuple = dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> pi({tuple, default}, Ty) end),

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
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> tuple_keys(V) -- maps:keys(Tn) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [(tuple_keys(V) -- maps:keys(AllTuples)) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherTupleKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherTuples = maps:from_list([{Length, dnf_var_ty_tuple:substitute(DefaultTuple, SubstituteMap, Memo, fun(Ty) -> pi({tuple, Length}, Ty) end)} || Length <- OtherTupleKeys]),

  % all explicit keys are now all defined tuples and all newly explicit tuples after default substitution
  AllKeys = maps:keys(Tn) ++ maps:keys(NewDefaultOtherTuples),

  % {alpha, 0 => alpha} with alpha := {1} ==> {0, 1 => {1}}
  % for explicit tuples, collect all other lengths into a new map, yielding a list of maps
  % merge (union) these maps into NewOtherTuples
  NewOtherTuples = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, Tn) of
            true ->
            dnf_var_ty_tuple:substitute(maps:get(Key, Tn), SubstituteMap, Memo, fun(Ty) -> pi({tuple, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherTuples, NewDefaultTuple)
          end}
                                            end, AllKeys)),

  {NewDefaultTuple, 
    dnf_var_ty_bool:substitute(T0, SubstituteMap, Memo, fun(Ty) -> pi({tuple, 0}, Ty) end), 
    dnf_var_ty_ref:substitute(T1, SubstituteMap, Memo, fun(Ty) -> pi({tuple, 1}, Ty) end), 
    NewOtherTuples}.

multi_substitute_fun(DefaultFunction, AllFunctions, SubstituteMap, Memo) ->
  % see multi_substitute for comments
  % TODO refactor abstract into one function for both tuples and funcions
  NewDefaultFunction = dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> pi({function, default}, Ty) end),
  AllVars = dnf_var_ty_function:all_variables(DefaultFunction),
  % TODO erlang 26 map comprehensions
  Keys = maps:fold(fun(K,V,AccIn) -> case lists:member(K, AllVars) of true -> function_keys(V) -- maps:keys(AllFunctions) ++ AccIn; _ -> AccIn end end, [], SubstituteMap),
  % Keys = [function_keys(V) || K := V <- SubstituteMap, lists:member(K, AllVars)],
  OtherFunctionKeys = lists:usort(lists:flatten(Keys)),
  NewDefaultOtherFunctions = maps:from_list([{Length, dnf_var_ty_function:substitute(DefaultFunction, SubstituteMap, Memo, fun(Ty) -> pi({function, Length}, Ty) end)} || Length <- OtherFunctionKeys]),
  AllKeys = maps:keys(AllFunctions) ++ maps:keys(NewDefaultOtherFunctions),

  NewOtherFunctions = maps:from_list(lists:map(fun(Key) ->
    {Key, case maps:is_key(Key, AllFunctions) of
            true -> dnf_var_ty_function:substitute(maps:get(Key, AllFunctions), SubstituteMap, Memo, fun(Ty) -> pi({function, Key}, Ty) end);
            _ -> maps:get(Key, NewDefaultOtherFunctions, NewDefaultFunction)
          end}
                                            end, AllKeys)),

  {NewDefaultFunction, NewOtherFunctions}.

has_ref({ty_ref, 0}, _) -> false;
has_ref({ty_ref, 1}, _) -> false;
has_ref(TyRef1 = {ty_ref, _}, TyRef) -> has_ref(ty_ref:load(TyRef1), TyRef);
has_ref(#ty{list = Lists, tuple = {Default, T0, T1, AllTuple}, function = {DefaultF, AllFunction}}, TyRef) ->
  % TODO sanity remove
  false = dnf_var_ty_bool:has_ref(T0, TyRef), % should never happen
  false = dnf_var_ty_tuple:has_ref(Default, TyRef), % should never happen
  false = dnf_var_ty_function:has_ref(DefaultF, TyRef), % should never happen
  dnf_var_ty_list:has_ref(Lists, TyRef)
  orelse
  dnf_var_ty_ref:has_ref(T1, TyRef)
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
  {D, _, _, _TM} = Ty#ty.tuple,
  D;
pi({tuple, 0}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_, T0, _, _} = Ty#ty.tuple,
  T0;
pi({tuple, 1}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {_, _, T1, _} = Ty#ty.tuple,
  T1;
pi({tuple, Len}, TyRef) ->
  Ty = ty_ref:load(TyRef),
  {D, _, _, TM} = Ty#ty.tuple,
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

all_variables({ty_ref, 0}) -> [];
all_variables({ty_ref, 1}) -> [];
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
  ++ dnf_var_ty_tuple:mall_variables(Tuples)
  ++ dnf_var_ty_function:mall_variables(Functions)).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% TODO tuples use diff on a not yet finished recursively defined type reference
recursive_definition_test() ->
  test_utils:reset_ets(),
  Lists = ty_ref:new_ty_ref(),
  ListsBasic = ty_ref:new_ty_ref(),

  Alpha = ty_variable:new("alpha"),
  AlphaTy = ty_rec:variable(Alpha),

  %    nil
  % U (alpha, Lists)
  EmptyRec = ty_ref:load(empty()),
  NewTyRec = (ty_ref:load(empty()))#ty{
    tuple = set_tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_product:tuple(ty_tuple:tuple([AlphaTy, Lists])))),
    atom = dnf_var_ty_atom:ty_atom(ty_atom:finite([nil]))
  },
  ty_ref:define_ty_ref(Lists, NewTyRec),

  io:format(user, "Defined recursive list type: ~s~n", [ty_rec:print(Lists)]),
  error(todo),

  ok.

any_0tuple_test() ->
  test_utils:reset_ets(),
  AnyTuple = ty_rec:tuple(0, dnf_var_ty_bool:bool(bdd_bool:any())),
  AnyTuple2 = ty_rec:tuple(0, dnf_var_ty_bool:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

any_1tuple_test() ->
  test_utils:reset_ets(),
  AnyTuple = ty_rec:tuple(1, dnf_var_ty_ref:ref(ty_rec:any())),
  AnyTuple2 = ty_rec:tuple(1, dnf_var_ty_ref:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

nonempty_function_test() ->
  Function = ty_rec:function(1, dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function([ty_rec:empty()], ty_rec:any())))),
  Function2 = ty_rec:function(1, dnf_var_ty_function:any()),
  true = ty_rec:is_subtype(Function, Function2),
  true = ty_rec:is_subtype(Function2, Function),
  ok.

-endif.
