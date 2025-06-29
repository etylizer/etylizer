-module(ty_rec).

-compile([export_all, nowarn_export_all]).

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

-type type() :: #ty{} | any | empty.
-type local_cache() :: ty_node:local_cache().

-define(RECORD, ty).
-include("utils/record_utils.hrl").


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

difference(empty, _T2) -> empty;
difference(any, T2) -> negate(T2);
difference(T1, empty) -> T1;
difference(_T1, any) -> empty;
difference(T1, T2) ->
  simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:difference(Left, Right) end, T1, T2)).

% TODO is there a better way to simplify edge cases?
simpl_to_repr(Ty) -> 
  case any0() of
    Ty -> any();
    _ -> 
    case empty0() of
      Ty -> empty();
      _ -> Ty
    end
  end.

functions(Fs) -> (empty0())#ty{ty_functions = Fs}.
tuples(Ts) -> (empty0())#ty{ty_tuples = Ts}.
atom(A) -> (empty0())#ty{dnf_ty_atom = A}.
interval(A) -> (empty0())#ty{dnf_ty_interval = A}.
list(A) -> (empty0())#ty{dnf_ty_list = A}.
predefined(A) -> (empty0())#ty{dnf_ty_predefined = A}.
bitstring(A) -> (empty0())#ty{dnf_ty_bitstring = A}.
map(A) -> (empty0())#ty{dnf_ty_map = A}.

% Converter used by ty_parser
% to convert from a map encoded in the 2-arity tuple part to the map part
tuple_to_map(#ty{ty_tuples = {_, #{2 := TupleDnf}}}) ->
  [{[T], [], _}] = dnf_ty_tuple:dnf(TupleDnf),
  DnfMap = dnf_ty_map:singleton(T),
  map(DnfMap).


% ===
% Tallying
% ===

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
