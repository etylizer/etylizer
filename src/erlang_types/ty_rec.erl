-module(ty_rec).

-export([
  compare/2,
  equal/2,
  any/0,
  empty/0,
  is_empty/2,
  normalize/3,
  union/2,
  difference/2,
  intersect/2,
  negate/1,
  all_variables/2,
  unparse/2,

  functions/1,
  tuples/1,
  atom/1,
  interval/1,
  list/1,
  predefined/1,
  bitstring/1,
  map/1,

  tuple_to_map/1,
  is_literal_empty/1
]).

-record(ty, 
  {
    dnf_ty_predefined = dnf_ty_predefined:empty(),
    dnf_ty_atom = dnf_ty_atom:empty(),
    dnf_ty_interval = dnf_ty_interval:empty(),
    dnf_ty_list = dnf_ty_list:empty(),
    dnf_ty_bitstring = dnf_ty_bitstring:empty(),
    ty_tuples = ty_tuples:empty(),
    ty_functions = ty_functions:empty(),
    dnf_ty_map = dnf_ty_map:empty()
  }).

% all components (=> Erlang module names) of the type record
-type type_module() :: 
    dnf_ty_predefined | dnf_ty_atom | dnf_ty_interval 
  | dnf_ty_list | dnf_ty_bitstring | ty_tuples 
  | ty_functions | dnf_ty_map.
-type ast_ty() :: ast:ty().
-type type() :: #ty{} | any | empty.
-type local_cache() :: ty_node:local_cache().
-type variable() :: ty_variable:type().
-type all_variables_cache() :: term(). %TODO
-type set_of_constraint_sets() :: contraint_set:set_of_constraint_sets().
-type monomorphic_variables() :: etally:monomorphic_variables().


-spec compare(type(), type()) -> lt | gt | eq.
compare(any, any) -> eq;
compare(empty, empty) -> eq;
compare(any, _) -> gt;
compare(empty, _) -> lt;
compare(_, any) -> lt;
compare(_, empty) -> gt;
compare(Ty1, Ty2) ->
  binary_fold(fun
        (Module, V1, V2, eq) -> Module:compare(V1, V2);
        (_, _, _, R) -> R
      end, 
      eq,
      Ty1, Ty2).

-spec equal(type(), type()) -> boolean().
equal(Ty1, Ty2) -> compare(Ty1, Ty2) =:= eq.

-spec any0() -> type().
any0() ->
  map(fun(Field, _Value) -> Field:any() end, #ty{}).

-spec any() -> type().
any() -> any.

-spec empty0() -> type().
empty0() ->
  #ty{}.

-spec empty() -> type().
empty() -> empty.
  

-spec is_empty(type(), local_cache()) -> {boolean(), local_cache()}.
is_empty(any, Cache) -> {false, Cache};
is_empty(empty, Cache) -> {true, Cache};
is_empty(Ty, Cache) ->
  fold(fun
        (_, _, {false, LC0}) -> {false, LC0};
        (Module, Value, {true, LC0}) -> 
          Module:is_empty(Value, LC0)
      end, 
      {true, Cache},
      Ty).

-spec is_literal_empty(type()) -> boolean().
is_literal_empty(empty) -> true;
is_literal_empty(Z) -> Z =:= #ty{}.

-spec negate(type()) -> type().
negate(empty) -> any;
negate(any) -> empty;
negate(T1) ->
  simpl_to_repr(map(fun(Module, Value) -> Module:negate(Value) end, T1)).

-spec union(type(), type()) -> type().
union(empty, T2) -> T2;
union(any, _T2) -> any;
union(T1, empty) -> T1;
union(_T1, any) -> any;
union(T1, T2) ->
  simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:union(Left, Right) end, T1, T2)).

-spec intersect(type(), type()) -> type().
intersect(empty, _T2) -> empty;
intersect(any, T2) -> T2;
intersect(_T1, empty) -> empty;
intersect(T1, any) -> T1;
intersect(T1, T2) ->
  simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:intersect(Left, Right) end, T1, T2)).

-spec difference(T, T) -> T when T :: type().
difference(empty, _T2) -> empty;
difference(any, T2) -> negate(T2);
difference(T1, empty) -> T1;
difference(_T1, any) -> empty;
difference(T1, T2) ->
  simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:difference(Left, Right) end, T1, T2)).

% TODO is there a better way to simplify edge cases?
-spec simpl_to_repr(type()) -> type().
simpl_to_repr(Ty) -> 
  case any0() of
    Ty -> any();
    _ -> 
    case empty0() of
      Ty -> empty();
      _ -> Ty
    end
  end.

-spec functions(ty_functions:type()) -> type().
functions(Fs) -> (empty0())#ty{ty_functions = Fs}.

-spec tuples(ty_tuples:type()) -> type().
tuples(Ts) -> (empty0())#ty{ty_tuples = Ts}.

-spec atom(dnf_ty_atom:type()) -> type().
atom(A) -> (empty0())#ty{dnf_ty_atom = A}.

-spec interval(dnf_ty_interval:type()) -> type().
interval(A) -> (empty0())#ty{dnf_ty_interval = A}.

-spec list(dnf_ty_list:type()) -> type().
list(A) -> (empty0())#ty{dnf_ty_list = A}.

-spec predefined(dnf_ty_predefined:type()) -> type().
predefined(A) -> (empty0())#ty{dnf_ty_predefined = A}.

-spec bitstring(dnf_ty_bitstring:type()) -> type().
bitstring(A) -> (empty0())#ty{dnf_ty_bitstring = A}.

-spec map(dnf_ty_map:type()) -> type().
map(A) -> (empty0())#ty{dnf_ty_map = A}.

% Converter used by ty_parser
% to convert from a map encoded in the 2-arity tuple part to the map part
-spec tuple_to_map(type()) -> type().
tuple_to_map(#ty{ty_tuples = {_, #{2 := TupleDnf}}}) ->
  [{[T], [], _}] = dnf_ty_tuple:dnf(TupleDnf),
  DnfMap = dnf_ty_map:singleton(T),
  map(DnfMap).

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables(any, _Cache) -> sets:new();
all_variables(empty, _Cache) -> sets:new();
all_variables(TyRec, Cache) ->
  fold(fun
        (Module, Value, Vars) -> 
          sets:union(Vars, Module:all_variables(Value, Cache))
      end, 
      sets:new(),
      TyRec).


% ===
% Tallying
% ===
-spec normalize(type(), monomorphic_variables(), ST) -> {set_of_constraint_sets(), ST}.
normalize(any, _Fixed, Cache) -> {[], Cache};
normalize(empty, _Fixed, Cache) -> {[[]], Cache};
normalize(TyRec, Fixed, ST) ->
  fold(fun
        (_, _, {[], LC0}) -> {[], LC0};
        (Module, Value, {ConstrsCurrent, LC0}) -> 
          {Normalized, LC1} = Module:normalize(Value, Fixed, LC0),
          {constraint_set:meet(ConstrsCurrent, Normalized, Fixed), LC1}
      end, 
      {[[]], ST},
      TyRec).

% ===
% Unparse
% ===
-spec unparse(type(), ST) -> {ast_ty(), ST}.
unparse(any, Cache) -> {{predef, any}, Cache};
unparse(empty, Cache) -> {{predef, none}, Cache};
unparse(Ty, ST) ->
  {Z, ST2} = 
  fold(fun 
         (Module, Value, {Acc, ST0}) -> 
           {P, ST1} = Module:unparse(Value, ST0), 
           {Acc ++ [unparse_any(Module, P)], ST1}
       end, 
       {[], ST}, 
       Ty),
  {ast_lib:mk_union(Z), ST2}.

% TODO only intersect if needed
-spec unparse_any(type_module(), ast_ty()) -> ast_ty().
unparse_any(dnf_ty_predefined, Result) -> 
  ast_lib:mk_intersection(
   [{union, [{empty_list}, {predef, float}, {predef, pid}, {predef, port}, {predef, reference}]}, 
    ast_lib:mk_union(Result)]);
unparse_any(dnf_ty_atom, Result) -> 
  ast_lib:mk_intersection([{predef, atom}, Result]);
unparse_any(dnf_ty_interval, Result) -> 
  ast_lib:mk_intersection([{predef, integer}, Result]);
unparse_any(dnf_ty_list, Result) -> 
  ast_lib:mk_intersection([{improper_list, {predef, any}, {predef, any}}, Result]);
unparse_any(dnf_ty_bitstring, Result) -> 
  ast_lib:mk_intersection([{bitstring}, Result]);
unparse_any(ty_tuples, Result = {tuple, _}) -> Result;
unparse_any(ty_tuples, Result) -> 
  ast_lib:mk_intersection([{tuple_any}, Result]);
unparse_any(ty_functions, Result = {fun_full, _, _}) -> Result;
unparse_any(ty_functions, Result) -> 
  ast_lib:mk_intersection([{fun_simple}, Result]);
unparse_any(dnf_ty_map, Result) -> 
  ast_lib:mk_intersection([{map_any}, Result]);
unparse_any(Module, _) -> 
  error({no_unparse_implemented, Module}).


% record helper functions

% these helper function assume a fixed order for records in Erlang
% with the first index being the record name
-spec map(fun((Module :: type_module(), Value) -> Value), type()) -> type(). % when Value :: Module:type()
map(Map, Record) ->
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Rec) -> 
      OldValue = element(Index, Record),
      setelement(Index, Rec, Map(Field, OldValue))
    end, 
    Record, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

% same as map, but mapping over two records at once
-spec binary_map(fun((Module :: type_module(), Value, Value) -> Value), type(), type()) -> type(). % when Value :: Module:type()
binary_map(BinaryMap, Record1, Record2) ->
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Rec) -> 
      OldLeftValue = element(Index, Record1),
      OldRightValue = element(Index, Record2),
      setelement(Index, Rec, BinaryMap(Field, OldLeftValue, OldRightValue))
    end, 
    Record1, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

-spec fold(fun((Module :: type_module(), Value, Acc) -> Value), Acc, type()) -> type(). % when Value :: Module:type()
fold(Fold, BaseAcc, Record) ->
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      Fold(Field, element(Index, Record), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

-spec binary_fold(fun((Module :: type_module(), Value, Value, Acc) -> Value), Acc, type(), type()) -> type(). % when Value :: Module:type()
binary_fold(BinaryFold, BaseAcc, Record1, Record2) ->
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      BinaryFold(Field, element(Index, Record1), element(Index, Record2), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).
