-module(ty_rec).

-export_type([ty_rec/0, ty_ref/0]).

% co-recursive functions on types
-export([is_empty/1, is_empty_start/1, normalize_start/2]).
-export([is_empty_corec/2, normalize_corec/3]).

-export([empty/0, any/0]).
-export([union/2, negate/1, intersect/2, diff/2, is_any/1]).
-export([tuple_keys/1, function_keys/1]).

% additional type constructors (hash consed)
-export([predef/0, predef/1, variable/1, atom/1, interval/1, tuple/2, map/1]).
% additional type constructors (record only)
-export([tuple_to_map/1, s_interval/0, s_intersect/2, s_union/2, s_negate/1, s_any/0, s_empty/0, s_map/0, s_predef/1, s_variable/1, s_atom/1, s_interval/1, s_function/2, s_tuple/2, s_map/1, s_list/1, s_tuple/0, s_function/0]).
% type constructors with type refs
-export([list/1, function/2]).
% top type constructors
-export([list/0, function/0, atom/0, interval/0, tuple/0, map/0, ty_of/7]).

-export([is_equivalent/2, is_subtype/2]).

-export([substitute/2, substitute/3, pi/2, all_variables/1, all_variables/2]).

-export([raw_transform/2, transform/2, print/1]).

-include("sanity.hrl").

-record(ty, {predef, atom, interval, list, tuple, function, map}).


-type ty_rec() :: #ty{}.
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

ty_of(Predef, Atom, Int, List, Tuple, Function, Map) ->
  #ty{predef = Predef, atom = Atom, interval = Int, list = List, tuple = Tuple, function = Function, map = Map}.

is_subtype(TyRef1, TyRef2) ->
  NewTy = intersect(TyRef1, ty_rec:negate(TyRef2)),
  is_empty_start(NewTy).

is_equivalent(TyRef1, TyRef2) ->
  is_subtype(TyRef1, TyRef2) andalso is_subtype(TyRef2, TyRef1).

maybe_intersect(Z2, Other, Intersect) ->
  case subty:is_subty(symtab:empty(), Z2, Other) of %TODO symtab?
    true -> Z2;
    false -> Intersect([Other, Z2])
  end.

raw_transform(TyRef, Ops =
  #{
    any_list := Lists,
    any_map := Maps,
    any_tuple := Tuples,
    any_function := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    any_predef := Predef,
    union := Union,
    intersect := Intersect
  }) ->
  #ty{predef = P, atom = A, interval = I, list = L, map = M, tuple = T, function = F} = ty_ref:load(TyRef),

  NP = Intersect([Predef(), dnf_var_ty_predef:raw_transform(P, Ops)]),
  NA = Intersect([Atoms(), dnf_var_ty_atom:raw_transform(A, Ops)]),
  NI = Intersect([Intervals(), dnf_var_ty_interval:raw_transform(I, Ops)]),
  NL = Intersect([Lists(), dnf_var_ty_list:raw_transform(L, Ops)]),
  NM = Intersect([Maps(), dnf_var_ty_map:raw_transform(M, Ops)]),
  NT = Intersect([Tuples(), ty_tuples:raw_transform(T, Ops)]),
  NF = Intersect([Functions(), ty_functions:raw_transform(F, Ops)]),

  Union([NP, NA, NI, NL, NM, NT, NF]).

transform(TyRef, Ops) ->
  % Do things twice, pos and neg
  Pos = transform_p(TyRef, Ops),
  Neg = transform_p(ty_rec:negate(TyRef), Ops),

%%  io:format(user, "Positive:~n~p~n", [Pos]),
%%  io:format(user, "Negative:~n~p~n", [Neg]),
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

% ty_rec:ty() -> ast_erl:ty()
transform_p(TyRef, Ops =
  #{
    any_list := Lists,
    any_tuple := Tuples,
    any_function := Functions,
    any_int := Intervals,
    any_atom := Atoms,
    any_predef := Predef,
    any_map := Maps,
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
        #ty{predef = P, atom = A, interval = I, list = L, map = M, tuple = T, function = F} = ty_ref:load(TyR),
        NP = maybe_intersect(dnf_var_ty_predef:transform(P, Ops), Predef(), Intersect),
        NA = maybe_intersect(dnf_var_ty_atom:transform(A, Ops), Atoms(), Intersect),
        NI = maybe_intersect(dnf_var_ty_interval:transform(I, Ops), Intervals(), Intersect),
        NL = maybe_intersect(dnf_var_ty_list:transform(L, Ops), Lists(), Intersect),
        NM = maybe_intersect(dnf_var_ty_map:transform(M, Ops), Maps(), Intersect),
        NT = maybe_intersect(ty_tuples:transform(T, Ops), Tuples(), Intersect),
        NF = maybe_intersect(ty_functions:transform(F, Ops), Functions(), Intersect),
        Intersect(NewVars ++ NewVarsN ++ [Union([NP, NA, NI, NL, NT, NF, NM])])
    end
           end, DnfMap),

  Union(maps:values(Mapped)).

% TODO refactor this properly it's ugly
prepare(TyRef) ->
  #ty{predef = P, atom = A, interval = I, list = L, tuple = {DT, T}, function = {DF, F}, map = M} = ty_ref:load(TyRef),
  VarMap = #{},

  PDnf = dnf_var_ty_predef:get_dnf(P),
  ADnf = dnf_var_ty_atom:get_dnf(A),
  IDnf = dnf_var_ty_interval:get_dnf(I),
  LDnf = dnf_var_ty_list:get_dnf(L),
  MDnf = dnf_var_ty_map:get_dnf(M),

  PMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:predef(dnf_var_ty_predef:predef(Ty))} end, PDnf),
  AMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:atom(dnf_var_ty_atom:ty_atom(Ty))} end, ADnf),
  IMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:interval(dnf_var_ty_interval:int(Ty))} end, IDnf),
  LMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:list(dnf_var_ty_list:list(Ty))} end, LDnf),
  MMapped = lists:map(fun({Pv, Nv, Ty}) -> {{Pv, Nv}, ty_rec:map(dnf_var_ty_map:map(Ty))} end, MDnf),


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

  AllKinds = lists:flatten([PMapped, AMapped, IMapped, LMapped, MMapped, TupleMapped, FunctionMapped, TupleExplicitMapped, FunctionExplicitMapped]),

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
  TopTypes = [ty_rec:atom(), ty_rec:interval(), ty_rec:tuple(), ty_rec:function(), ty_rec:list(), ty_rec:predef(), ty_rec:map()],
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
  S = fun(E) -> sets:from_list(E, [{version, 2}]) end,
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
  S = fun(E) -> sets:from_list(E, [{version, 2}]) end,
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

% currently not needed
% extract_variables(Ty = #ty{ predef = P, atom = A, interval = I, list = L, tuple = T, function = F, map = M }) ->
%   PossibleVars = lists:foldl(fun(E, Acc) ->
%     sets:intersection(sets:from_list(E, [{version, 2}]), Acc)
%               end, sets:from_list(dnf_var_ty_predef:all_variables(P), [{version, 2}]),
%     [
%       dnf_var_ty_atom:all_variables(A),
%       dnf_var_ty_interval:all_variables(I),
%       dnf_var_ty_list:all_variables(L),
%       dnf_var_ty_tuple:mall_variables(T, #{}),
%       dnf_var_ty_function:mall_variables(F, #{}),
%       dnf_var_ty_map:all_variables(M)
%     ]),
%   {Vars, NewTy} = lists:foldl(fun(Var, {ExtractedVars, TTy}) ->
%     case ty_rec:is_subtype(ty_rec:variable(Var), TTy) of
%       true ->
%         {[Var | ExtractedVars],
%         ty_rec:diff(TTy, ty_rec:variable(Var))};
%       false -> {ExtractedVars, TTy}
%     end
%                       end, {[], ty_ref:store(Ty)}, sets:to_list(PossibleVars)),
%   {Vars, NewTy}.

% ======
% Type constructors
% ======
s_empty() ->
  #ty{
    predef = dnf_var_ty_predef:empty(),
    atom = dnf_var_ty_atom:empty(),
    interval = dnf_var_ty_interval:empty(),
    list = dnf_var_ty_list:empty(),
    tuple = ty_tuples:empty(),
    function = ty_functions:empty(),
    map = dnf_var_ty_map:empty()
  }.

-spec empty() -> ty_ref().
empty() ->
  ty_ref:store(#ty{
    predef = dnf_var_ty_predef:empty(),
    atom = dnf_var_ty_atom:empty(),
    interval = dnf_var_ty_interval:empty(),
    list = dnf_var_ty_list:empty(),
    tuple = ty_tuples:empty(),
    function = ty_functions:empty(),
    map = dnf_var_ty_map:empty()
  }).

-spec any() -> ty_ref().
any() ->
  ty_ref:any().

s_any() ->
  ty_ref:load(ty_ref:any()).

s_variable(Var) ->
  #ty{
    predef = dnf_var_ty_predef:var(Var),
    atom = dnf_var_ty_atom:var(Var),
    interval = dnf_var_ty_interval:var(Var),
    list = dnf_var_ty_list:var(Var),
    tuple = ty_tuples:var(Var),
    function = ty_functions:var(Var),
    map = dnf_var_ty_map:var(Var)
  }.
-spec variable(ty_variable()) -> ty_ref().
variable(Var) ->
  ty_ref:store(#ty{
    predef = dnf_var_ty_predef:var(Var),
    atom = dnf_var_ty_atom:var(Var),
    interval = dnf_var_ty_interval:var(Var),
    list = dnf_var_ty_list:var(Var),
    tuple = ty_tuples:var(Var),
    function = ty_functions:var(Var),
    map = dnf_var_ty_map:var(Var)
  }).

s_list(List) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ list = List }.


list() -> list(dnf_var_ty_list:any()).
list(List) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ list = List }).

s_atom(Atom) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ atom = Atom }.

-spec atom(ty_atom()) -> ty_ref().
atom(Atom) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ atom = Atom }).

-spec atom() -> ty_ref().
atom() -> atom(dnf_var_ty_atom:any()).

s_interval(Interval) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ interval = Interval }.

s_interval() -> s_interval(dnf_var_ty_interval:any()).

-spec interval(interval()) -> ty_ref().
interval(Interval) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ interval = Interval }).

-spec interval() -> ty_ref().
interval() -> interval(dnf_var_ty_interval:any()).

s_predef(Predef) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ predef = Predef }.
predef(Predef) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ predef = Predef }).
predef() -> predef(dnf_var_ty_predef:any()).

s_tuple({default, Sizes}, Tuple) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  Empty#ty{ tuple = {Tuple, NotCaptured}};
s_tuple(ComponentSize, Tuple) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), #{ComponentSize => Tuple}} }.

tuple({default, Sizes}, Tuple) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_tuple:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {Tuple, NotCaptured}});
tuple(ComponentSize, Tuple) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = {dnf_var_ty_tuple:empty(), #{ComponentSize => Tuple}} }).

s_tuple() ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ tuple = ty_tuples:any() }.

-spec tuple() -> ty_ref().
tuple() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ tuple = ty_tuples:any() }).

s_function({default, Sizes}, Function) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_function:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  (Empty#ty{ function = {Function, NotCaptured}});
s_function(ComponentSize, Fun) ->
  Empty = ty_ref:load(empty()),
  (Empty#ty{ function = {dnf_var_ty_function:empty(), #{ComponentSize => Fun} }}).

function({default, Sizes}, Function) ->
  NotCaptured = maps:from_list(lists:map(fun(Size) -> {Size, dnf_var_ty_function:empty()} end, Sizes)),
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {Function, NotCaptured}});
function(ComponentSize, Fun) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = {dnf_var_ty_function:empty(), #{ComponentSize => Fun} }}).

s_function() ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ function = ty_functions:any() }.

-spec function() -> ty_ref().
function() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ function = ty_functions:any() }).

s_map(Map) ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ map = Map }.
map(Map) ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ map = Map }).

s_map() ->
  Empty = ty_ref:load(empty()),
  Empty#ty{ map = dnf_var_ty_map:any() }.

% Converter used by ast_to_erlang_ty
% to convert from a tuple-encoded map to a map
tuple_to_map(#ty{tuple = {_, #{2 := VarTupleDnf}}}) ->
  [{[], [], DnfTyTuple}] = dnf_var_ty_tuple:get_dnf(VarTupleDnf),
  [{[T], [], _}] = dnf_ty_tuple:get_dnf(DnfTyTuple),
  DnfMap = dnf_ty_map:map(T),
  VarDnfMap = dnf_var_ty_map:map(DnfMap),
  ty_rec:s_map(VarDnfMap).

-spec map() -> ty_ref().
map() ->
  Empty = ty_ref:load(empty()),
  ty_ref:store(Empty#ty{ map = dnf_var_ty_map:any() }).


% ======
% Boolean operations
% ======

-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(TyRef1, TyRef2) ->
  ty_ref:op_cache(intersect, {TyRef1, TyRef2},
    fun() ->
      #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = T1, function = F1, map = M1} = ty_ref:load(TyRef1),
      #ty{predef = P2, atom = A2, interval = I2, list = L2, tuple = T2, function = F2, map = M2} = ty_ref:load(TyRef2),
      ty_ref:store(#ty{
        predef = dnf_var_ty_predef:intersect(P1, P2),
        atom = dnf_var_ty_atom:intersect(A1, A2),
        interval = dnf_var_ty_interval:intersect(I1, I2),
        list = dnf_var_ty_list:intersect(L1, L2),
        tuple = ty_tuples:intersect(T1, T2),
        function = ty_functions:intersect(F1, F2),
        map = dnf_var_ty_map:intersect(M1, M2)
      })
    end
    ).

-spec negate(ty_ref()) -> ty_ref().
negate(TyRef1) ->
  ty_ref:op_cache(negate, {TyRef1},
    fun() ->
      #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = T, function = F, map = M1} = ty_ref:load(TyRef1),
      ty_ref:store(#ty{
        predef = dnf_var_ty_predef:negate(P1),
        atom = dnf_var_ty_atom:negate(A1),
        interval = dnf_var_ty_interval:negate(I1),
        list = dnf_var_ty_list:negate(L1),
        tuple = ty_tuples:negate(T),
        function = ty_functions:negate(F),
        map = dnf_var_ty_map:negate(M1)
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

s_union(A, B) ->
  s_negate(s_intersect(s_negate(A), s_negate(B))).

s_negate(#ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = T, function = F, map = M1}) ->
  #ty{
    predef = dnf_var_ty_predef:negate(P1),
    atom = dnf_var_ty_atom:negate(A1),
    interval = dnf_var_ty_interval:negate(I1),
    list = dnf_var_ty_list:negate(L1),
    tuple = ty_tuples:negate(T),
    function = ty_functions:negate(F),
    map = dnf_var_ty_map:negate(M1)
  }.

s_intersect(TyRec1, TyRec2) ->
  #ty{predef = P1, atom = A1, interval = I1, list = L1, tuple = T1, function = F1, map = M1} = TyRec1,
  #ty{predef = P2, atom = A2, interval = I2, list = L2, tuple = T2, function = F2, map = M2} = TyRec2,
  #ty{
    predef = dnf_var_ty_predef:intersect(P1, P2),
    atom = dnf_var_ty_atom:intersect(A1, A2),
    interval = dnf_var_ty_interval:intersect(I1, I2),
    list = dnf_var_ty_list:intersect(L1, L2),
    tuple = ty_tuples:intersect(T1, T2),
    function = ty_functions:intersect(F1, F2),
    map = dnf_var_ty_map:intersect(M1, M2)
  }.


is_empty(TyRef) -> is_empty_start(TyRef).

% only cache full-chained is_empty, never cache in-between emptiness which depends on the memoization set M
% we could do that if we knew the tyref at hand is not corecursive
is_empty_start(TyRef) ->
  % first try op-cache
  case ty_ref:is_empty_cached(TyRef) of
    R when R == true; R == false -> R;
    miss ->
      ty_ref:store_is_empty_cached(TyRef, is_empty_corec(TyRef, #{}))
  end.

is_empty_corec(TyRef, M) ->
  case M of
    #{TyRef := true} -> true; % co-definition
    _ -> 
      Ty = ty_ref:load(TyRef),
      MNew = M#{TyRef => true},
      dnf_var_ty_predef:is_empty(Ty#ty.predef)
        andalso dnf_var_ty_atom:is_empty(Ty#ty.atom)
        andalso dnf_var_ty_interval:is_empty(Ty#ty.interval)
        andalso dnf_var_ty_list:is_empty_corec(Ty#ty.list, MNew)
        andalso ty_tuples:is_empty_corec(Ty#ty.tuple, MNew)
        andalso ty_functions:is_empty_corec(Ty#ty.function, MNew)
        andalso dnf_var_ty_map:is_empty_corec(Ty#ty.map, MNew)
  end.

is_any(_Arg0) ->
  erlang:error(any_not_implemented). % TODO needed?

normalize_start(TyRef, Fixed) ->
  % first try op-cache
  case ty_ref:normalize_cached({TyRef, Fixed}) of
    miss ->
      ty_ref:store_normalize_cached({TyRef, Fixed}, normalize_corec(TyRef, Fixed, #{}));
    Cached -> Cached
  end.

normalize_corec(TyRef, Fixed, M) ->
  case M of
    #{TyRef := true} -> [[]]; % co-definition
    _ -> 
      Ty = ty_ref:load(TyRef),
      MNew = M#{TyRef => true},
      PredefNormalize = dnf_var_ty_predef:normalize_corec(Ty#ty.predef, Fixed, MNew),
      AtomNormalize = dnf_var_ty_atom:normalize_corec(Ty#ty.atom, Fixed, MNew),
      Both = constraint_set:merge_and_meet(PredefNormalize, AtomNormalize),
      case Both of
        [] -> [];
        _ ->

          IntervalNormalize = dnf_var_ty_interval:normalize_corec(Ty#ty.interval, Fixed, MNew),
          Res1 = constraint_set:merge_and_meet(Both, IntervalNormalize),
          case Res1 of
            [] -> [];
            _ ->
              begin
                    Res2 = ty_tuples:normalize_corec(Ty#ty.tuple, Fixed, MNew),
                    ResX = fun() -> constraint_set:merge_and_meet(Res1, Res2) end,
                    ResLists = fun() -> dnf_var_ty_list:normalize_corec(Ty#ty.list, Fixed, MNew) end,
                    Res3 = constraint_set:meet(ResX, ResLists),
                    case Res3 of
                      [] -> [];
                      _ ->
                        Res4 = ty_functions:normalize_corec(Ty#ty.function, Fixed, MNew),
                        Res5 = constraint_set:merge_and_meet(Res3, Res4),
                        case Res5 of
                          [] -> [];
                          _ ->
                            MapNormalize = dnf_var_ty_map:normalize_corec(Ty#ty.map, Fixed, MNew),
                            constraint_set:merge_and_meet(Res5, MapNormalize)
                        end
                    end
              end
          end
      end
    end.

substitute(TyRef, SubstituteMap) ->
  % the left map is the current projection
  % the right map is the original substitution map
  ?TIME(substitute, substitute(TyRef, SubstituteMap, #{})).

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
        tuple = T,
        function = F,
        map = Maps
      } = ty_ref:load(TyRef),


      case has_ref(Ty, TyRef) of
        true ->
          RecursiveNewRef = ty_ref:new_ty_ref(),
          Memo = OldMemo#{TyRef => RecursiveNewRef},
          NewTy = #ty{
            predef = ?TIME(vardef, dnf_var_ty_predef:substitute(Predef, SubstituteMap, Memo, fun(TTy) -> pi(predef, TTy) end)),
            atom = ?TIME(atom, dnf_var_ty_atom:substitute(Atoms, SubstituteMap, Memo, fun(TTy) -> pi(atom, TTy) end)),
            interval = ?TIME(int, dnf_var_ty_interval:substitute(Ints, SubstituteMap, Memo, fun(TTy) -> pi(interval, TTy) end)),
            list = ?TIME(list, dnf_var_ty_list:substitute(Lists, SubstituteMap, Memo, fun(TTy) -> pi(list, TTy) end)),
            tuple = ?TIME(multi_tuple, ty_tuples:substitute(T, SubstituteMap, Memo)),
            function = ?TIME(multi_fun, ty_functions:substitute(F, SubstituteMap, Memo)),
            map = ?TIME(map, dnf_var_ty_map:substitute(Maps, SubstituteMap, Memo, fun(TTy) -> pi(map, TTy) end))
          },
          ty_ref:define_ty_ref(RecursiveNewRef, NewTy);
        false ->
          NewTy = #ty{
            predef = ?TIME(vardef, dnf_var_ty_predef:substitute(Predef, SubstituteMap, OldMemo, fun(TTy) -> pi(predef, TTy) end)),
            atom = ?TIME(atom, dnf_var_ty_atom:substitute(Atoms, SubstituteMap, OldMemo, fun(TTy) -> pi(atom, TTy) end)),
            interval = ?TIME(int, dnf_var_ty_interval:substitute(Ints, SubstituteMap, OldMemo, fun(TTy) -> pi(interval, TTy) end)),
            list = ?TIME(list, dnf_var_ty_list:substitute(Lists, SubstituteMap, OldMemo, fun(TTy) -> pi(list, TTy) end)),
            tuple = ?TIME(multi_tuple, ty_tuples:substitute(T, SubstituteMap, OldMemo)),
            function = ?TIME(multi_fun, ty_functions:substitute(F, SubstituteMap, OldMemo)),
            map = ?TIME(map, dnf_var_ty_map:substitute(Maps, SubstituteMap, OldMemo, fun(TTy) -> pi(map, TTy) end))
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

has_ref(#ty{map = Maps, list = Lists, tuple = T, function = F}, TyRef) ->
  dnf_var_ty_map:has_ref(Maps, TyRef)
  orelse dnf_var_ty_list:has_ref(Lists, TyRef)
  orelse ty_tuples:has_ref(T, TyRef)
  orelse ty_functions:has_ref(F, TyRef).

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
  Ty#ty.function;
pi(map, TyRef) ->
  Ty = ty_ref:load(TyRef),
  Ty#ty.map.

all_variables(TyRef) -> all_variables(TyRef, #{}).
all_variables(TyRef, M) ->
  case M of
    #{TyRef := _} -> [];
    _ ->
      #ty{
        predef = Predefs,
        atom = Atoms,
        interval = Ints,
        list = Lists,
        tuple = Tuples,
        function = Functions,
        map = Maps
      } = ty_ref:load(TyRef),


      Mp = M#{TyRef => ok},
      lists:usort(
        dnf_var_ty_predef:all_variables(Predefs, M)
      ++ dnf_var_ty_atom:all_variables(Atoms, M)
      ++ dnf_var_ty_interval:all_variables(Ints, M)
      ++ dnf_var_ty_list:all_variables(Lists, Mp)
      ++ ty_tuples:all_variables(Tuples, Mp)
      ++ ty_functions:all_variables(Functions, Mp)
      ++ dnf_var_ty_map:all_variables(Maps, Mp)
      )
  end.

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

recursive_definition_test() ->
  test_utils:reset_ets(),
  Lists = ty_ref:new_ty_ref(),
  ListsBasic = ty_ref:new_ty_ref(),

  % nil
  Nil = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([nil]))),

  % (alpha, Lists)
  Alpha = ty_variable:new(alpha),
  AlphaTy = ty_rec:variable(Alpha),
  Tuple = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([AlphaTy, Lists])))),
  Recursive = ty_rec:union(Nil, Tuple),

  ty_ref:define_ty_ref(Lists, ty_ref:load(Recursive)),

  SomeBasic = ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([somebasic]))),
  SubstMap = #{Alpha => SomeBasic},
  Res = ty_rec:substitute(Lists, SubstMap),

  Tuple2 = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([SomeBasic, ListsBasic])))),
  Expected = ty_rec:union(Nil, Tuple2),
  % Expected is invalid after define_ty_ref!
  NewTy = ty_ref:define_ty_ref(ListsBasic, ty_ref:load(Expected)),

  true = ty_rec:is_equivalent(Res, NewTy),
  ok.

any_0tuple_test() ->
  AnyTuple = ty_rec:tuple(0, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([])))),
  AnyTuple2 = ty_rec:tuple(0, dnf_var_ty_tuple:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

any_tuple_test() ->
  AnyTuple = ty_rec:tuple(1, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([ty_rec:any()])))),
  AnyTuple2 = ty_rec:tuple(1, dnf_var_ty_tuple:any()),
  true = ty_rec:is_equivalent(AnyTuple, AnyTuple2),
  ok.

nonempty_function_test() ->
  Function = ty_rec:function(1, dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function([ty_rec:empty()], ty_rec:any())))),
  Function2 = ty_rec:function(1, dnf_var_ty_function:any()),
  true = ty_rec:is_subtype(Function, Function2),
  true = ty_rec:is_subtype(Function2, Function),
  ok.

% (X, (X, [])) where X = (X, []) | ([], [])
% test from Tchou/stt
% we need to construct this type manually
% mu type is not enough, X is chosen fresh on second encounter
sound_memoization_test() ->
  test_utils:reset_ets(),
  EmptyList = ast_lib:ast_to_erlang_ty(stdtypes:tempty_list(), symtab:empty()),

  X = ty_ref:new_ty_ref(),
  BasicTuple = dnf_ty_tuple:tuple(ty_tuple:tuple([EmptyList, EmptyList])),
  XTuple = dnf_ty_tuple:tuple(ty_tuple:tuple([X, EmptyList])),

  Union = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:union(BasicTuple, XTuple))),

  % X = (X, []) | ([], [])
  ty_ref:define_ty_ref(X, ty_ref:load(Union)),

  % Z = (X, [])
  Z = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([X, EmptyList])))),

  % (X, Z)
  Ty = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([X, Z])))),

  false = ty_rec:is_empty(Ty),

  ok.

% Test for #160
variable_translation_test() ->
  test_utils:reset_ets(),

  Tuple = ty_rec:tuple({default, []}, dnf_var_ty_tuple:any()),
  Var = ty_rec:variable(ty_variable:new(alpha)),
  Type = ty_rec:intersect(Tuple, Var),
  EqType = ast_lib:ast_to_erlang_ty(ast_lib:erlang_ty_to_ast(Type), symtab:empty()),
  true = ty_rec:is_equivalent(Type, EqType),

  ok.

% Test for #160
tuple_transformation_default_test() ->
  test_utils:reset_ets(),

  Tuple0 = ty_rec:tuple(0, dnf_var_ty_tuple:any()),
  Tuple1 = ty_rec:tuple(1, dnf_var_ty_tuple:any()),
  Tuple01 = ty_rec:union(Tuple0, Tuple1),
  Tuple1Again = ty_rec:intersect(Tuple1, Tuple01),

  EqType = ast_lib:ast_to_erlang_ty(ast_lib:erlang_ty_to_ast(Tuple1Again), symtab:empty()),
  true = ty_rec:is_equivalent(Tuple1Again, EqType),

  ok.

-endif.
