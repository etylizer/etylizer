-module(ty_rec).

-export([
  assert_valid/1,
  reorder/1,

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

  pi/2,
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

-export_type([type/0, type_record/0]).

% invariants
-etylizer({functions_exhaustive, off, [tuple_to_map/1]}).

-include("erlang_types.hrl").
-include("etylizer.hrl").

-record(ty, 
  {
    dnf_ty_predefined = dnf_ty_predefined:empty() :: dnf_ty_predefined:type(),
    dnf_ty_atom = dnf_ty_atom:empty() :: dnf_ty_atom:type(),
    dnf_ty_interval = dnf_ty_interval:empty() :: dnf_ty_interval:type(),
    dnf_ty_list = dnf_ty_list:empty() :: dnf_ty_list:type(),
    dnf_ty_bitstring = dnf_ty_bitstring:empty() :: dnf_ty_bitstring:type(),
    ty_tuples = ty_tuples:empty() :: ty_tuples:type(),
    ty_functions = ty_functions:empty() :: ty_functions:type(),
    dnf_ty_map = dnf_ty_map:empty() :: dnf_ty_map:type()
  }).

% all components (=> Erlang module names) of the type record
-type type() :: type_record() | any | empty.
-type type_record() :: #ty{}.

-type type_module() :: 
    dnf_ty_predefined | dnf_ty_atom | dnf_ty_interval 
  | dnf_ty_list | dnf_ty_bitstring | ty_tuples 
  | ty_functions | dnf_ty_map.
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().

-spec reorder(X) -> X when X :: type().
reorder(any) -> any;
reorder(empty) -> empty;
reorder(#ty{
    dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L, dnf_ty_bitstring = B,
    ty_tuples = T, ty_functions = F, dnf_ty_map = M
  }) ->
  simpl_to_repr(#ty{
    dnf_ty_predefined = dnf_ty_predefined:reorder(P),
    dnf_ty_atom = dnf_ty_atom:reorder(A),
    dnf_ty_interval = dnf_ty_interval:reorder(I),
    dnf_ty_list = dnf_ty_list:reorder(L),
    dnf_ty_bitstring = dnf_ty_bitstring:reorder(B),
    ty_tuples = ty_tuples:reorder(T),
    ty_functions = ty_functions:reorder(F),
    dnf_ty_map = dnf_ty_map:reorder(M)
  }).
% TODO unsupported dynamic function calls
% map(fun(Module, Value) -> Module:reorder(Value) end, Ty)

-spec assert_valid(type()) -> _.
assert_valid(any) -> ok;
assert_valid(empty) -> ok;
assert_valid(#ty{ty_tuples = T}) ->
  ty_tuples:assert_valid(T),
  ok.

% -spec find_atom_index(atom(), list()) -> pos_integer() | not_found.
% find_atom_index(Atom, List) ->
%     case lists:keyfind(Atom, 1, lists:zip(List, lists:seq(1, length(List)))) of
%         {Atom, Index} -> Index;
%         false -> not_found
%     end.

% -spec pi(type(), type_module()) -> type_module:type(). 
-spec pi
  (type_record(), dnf_ty_predefined) -> dnf_ty_predefined:type();
  (type_record(), dnf_ty_atom) -> dnf_ty_atom:type();
  (type_record(), dnf_ty_interval) -> dnf_ty_interval:type();
  (type_record(), dnf_ty_list) -> dnf_ty_list:type();
  (type_record(), dnf_ty_bitstring) -> dnf_ty_bitstring:type();
  (type_record(), ty_tuples) -> ty_tuples:type();
  (type_record(), ty_functions) -> ty_functions:type();
  (type_record(), dnf_ty_map) -> dnf_ty_map:type().
pi(#ty{dnf_ty_predefined = P}, dnf_ty_predefined) -> P;
pi(#ty{dnf_ty_atom = A}, dnf_ty_atom) -> A;
pi(#ty{dnf_ty_interval = I}, dnf_ty_interval) -> I;
pi(#ty{dnf_ty_list = L}, dnf_ty_list) -> L;
pi(#ty{dnf_ty_bitstring = B}, dnf_ty_bitstring) -> B;
pi(#ty{ty_tuples = T}, ty_tuples) -> T;
pi(#ty{ty_functions = F}, ty_functions) -> F;
pi(#ty{dnf_ty_map = M}, dnf_ty_map) -> M.
% pi(Ty, Mod) ->
%   Fields = record_info(fields, ty),
%   Ind = find_atom_index(Mod, Fields),
%   element(Ind + 1, Ty).

-spec compare(type(), type()) -> lt | gt | eq.
compare(any, any) -> eq;
compare(empty, empty) -> eq;
compare(any, _) -> gt;
compare(empty, _) -> lt;
compare(_, any) -> lt;
compare(_, empty) -> gt;
compare(#ty{
        dnf_ty_predefined = P1, dnf_ty_atom = A1, dnf_ty_interval = I1, 
        dnf_ty_list = L1, dnf_ty_bitstring = B1, ty_tuples = T1, 
        ty_functions = F1, dnf_ty_map = M1
    }, #ty{
        dnf_ty_predefined = P2, dnf_ty_atom = A2, dnf_ty_interval = I2, 
        dnf_ty_list = L2, dnf_ty_bitstring = B2, ty_tuples = T2, 
        ty_functions = F2, dnf_ty_map = M2
    }) ->
    
    maybe
        eq ?= dnf_ty_predefined:compare(P1, P2),
        eq ?= dnf_ty_atom:compare(A1, A2),
        eq ?= dnf_ty_interval:compare(I1, I2),
        eq ?= dnf_ty_list:compare(L1, L2),
        eq ?= dnf_ty_bitstring:compare(B1, B2),
        eq ?= ty_tuples:compare(T1, T2),
        eq ?= ty_functions:compare(F1, F2),
        dnf_ty_map:compare(M1, M2)
    end.

-spec equal(type(), type()) -> boolean().
equal(Ty1, Ty2) -> compare(Ty1, Ty2) =:= eq.

-spec any0() -> type_record().
any0() ->
    #ty{
        dnf_ty_predefined = dnf_ty_predefined:any(),
        dnf_ty_atom = dnf_ty_atom:any(),
        dnf_ty_interval = dnf_ty_interval:any(),
        dnf_ty_list = dnf_ty_list:any(),
        dnf_ty_bitstring = dnf_ty_bitstring:any(),
        ty_tuples = ty_tuples:any(),
        ty_functions = ty_functions:any(),
        dnf_ty_map = dnf_ty_map:any()
    }.
  % map(fun(Field, _Value) -> Field:any() end, #ty{}).

-spec any() -> type().
any() -> any.

-spec empty0() -> type_record().
empty0() ->
    #ty{
        dnf_ty_predefined = dnf_ty_predefined:empty(),
        dnf_ty_atom = dnf_ty_atom:empty(),
        dnf_ty_interval = dnf_ty_interval:empty(),
        dnf_ty_list = dnf_ty_list:empty(),
        dnf_ty_bitstring = dnf_ty_bitstring:empty(),
        ty_tuples = ty_tuples:empty(),
        ty_functions = ty_functions:empty(),
        dnf_ty_map = dnf_ty_map:empty()
    }.

-spec empty() -> type().
empty() -> empty.
  

-spec is_empty(type(), ST) -> {boolean(), ST} when ST :: is_empty_cache().
is_empty(any, Cache) -> {false, Cache};
is_empty(empty, Cache) -> {true, Cache};
is_empty(#ty{dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L, dnf_ty_bitstring = B, ty_tuples = T, ty_functions = F, dnf_ty_map = M}, Cache) ->
    maybe
        {true, Cache1} ?= dnf_ty_predefined:is_empty(P, Cache),
        {true, Cache2} ?= dnf_ty_atom:is_empty(A, Cache1),
        {true, Cache3} ?= dnf_ty_interval:is_empty(I, Cache2),
        {true, Cache4} ?= dnf_ty_list:is_empty(L, Cache3),
        {true, Cache5} ?= dnf_ty_bitstring:is_empty(B, Cache4),
        {true, Cache6} ?= ty_tuples:is_empty(T, Cache5),
        {true, Cache7} ?= ty_functions:is_empty(F, Cache6),
        dnf_ty_map:is_empty(M, Cache7)
    end.
% is_empty(Ty, Cache) ->
%   fold(fun
%         (_, _, {false, LC0}) -> {false, LC0};
%         (Module, Value, {true, LC0}) -> 
%           Module:is_empty(Value, LC0)
%       end, 
%       {true, Cache},
%       Ty).

-spec is_literal_empty(type()) -> boolean().
is_literal_empty(empty) -> true;
%is_literal_empty(Z) -> Z =:= #ty{}.
% FIXME 
is_literal_empty(Z) -> Z =:= #ty{
    dnf_ty_predefined = dnf_ty_predefined:empty(),
    dnf_ty_atom = dnf_ty_atom:empty(),
    dnf_ty_interval = dnf_ty_interval:empty(),
    dnf_ty_list = dnf_ty_list:empty(),
    dnf_ty_bitstring = dnf_ty_bitstring:empty(),
    ty_tuples = ty_tuples:empty(),
    ty_functions = ty_functions:empty(),
    dnf_ty_map = dnf_ty_map:empty()
  }.

-spec negate(type()) -> type().
negate(empty) -> any;
negate(any) -> empty;
negate(#ty{
        dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L,
        dnf_ty_bitstring = B, ty_tuples = T, ty_functions = F, dnf_ty_map = M
    }) ->
    simpl_to_repr(#ty{
        dnf_ty_predefined = dnf_ty_predefined:negate(P),
        dnf_ty_atom = dnf_ty_atom:negate(A),
        dnf_ty_interval = dnf_ty_interval:negate(I),
        dnf_ty_list = dnf_ty_list:negate(L),
        dnf_ty_bitstring = dnf_ty_bitstring:negate(B),
        ty_tuples = ty_tuples:negate(T),
        ty_functions = ty_functions:negate(F),
        dnf_ty_map = dnf_ty_map:negate(M)
    }).
% negate(T1) ->
%   simpl_to_repr(map(fun(Module, Value) -> Module:negate(Value) end, T1)).

-spec union(type(), type()) -> type().
union(empty, T2) -> T2;
union(any, _T2) -> any;
union(T1, empty) -> T1;
union(_T1, any) -> any;
union(#ty{
        dnf_ty_predefined = P1, dnf_ty_atom = A1, dnf_ty_interval = I1, 
        dnf_ty_list = L1, dnf_ty_bitstring = B1, ty_tuples = T1_1, 
        ty_functions = F1, dnf_ty_map = M1
    }, #ty{
        dnf_ty_predefined = P2, dnf_ty_atom = A2, dnf_ty_interval = I2, 
        dnf_ty_list = L2, dnf_ty_bitstring = B2, ty_tuples = T2_1, 
        ty_functions = F2, dnf_ty_map = M2
    }) ->
    
    simpl_to_repr(#ty{
        dnf_ty_predefined = dnf_ty_predefined:union(P1, P2),
        dnf_ty_atom = dnf_ty_atom:union(A1, A2),
        dnf_ty_interval = dnf_ty_interval:union(I1, I2),
        dnf_ty_list = dnf_ty_list:union(L1, L2),
        dnf_ty_bitstring = dnf_ty_bitstring:union(B1, B2),
        ty_tuples = ty_tuples:union(T1_1, T2_1),
        ty_functions = ty_functions:union(F1, F2),
        dnf_ty_map = dnf_ty_map:union(M1, M2)
    }).
% union(T1, T2) ->
%   simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:union(Left, Right) end, T1, T2)).

-spec intersect(type(), type()) -> type().
intersect(empty, _T2) -> empty;
intersect(any, T2) -> T2;
intersect(_T1, empty) -> empty;
intersect(T1, any) -> T1;
intersect(#ty{
        dnf_ty_predefined = P1, dnf_ty_atom = A1, dnf_ty_interval = I1, 
        dnf_ty_list = L1, dnf_ty_bitstring = B1, ty_tuples = T1_1, 
        ty_functions = F1, dnf_ty_map = M1
    }, #ty{
        dnf_ty_predefined = P2, dnf_ty_atom = A2, dnf_ty_interval = I2, 
        dnf_ty_list = L2, dnf_ty_bitstring = B2, ty_tuples = T2_1, 
        ty_functions = F2, dnf_ty_map = M2
    }) ->
    
    simpl_to_repr(#ty{
        dnf_ty_predefined = dnf_ty_predefined:intersect(P1, P2),
        dnf_ty_atom = dnf_ty_atom:intersect(A1, A2),
        dnf_ty_interval = dnf_ty_interval:intersect(I1, I2),
        dnf_ty_list = dnf_ty_list:intersect(L1, L2),
        dnf_ty_bitstring = dnf_ty_bitstring:intersect(B1, B2),
        ty_tuples = ty_tuples:intersect(T1_1, T2_1),
        ty_functions = ty_functions:intersect(F1, F2),
        dnf_ty_map = dnf_ty_map:intersect(M1, M2)
    }).
% intersect(T1, T2) ->
  % simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:intersect(Left, Right) end, T1, T2)).

-spec difference(T, T) -> T when T :: type().
difference(empty, _T2) -> empty;
difference(any, T2) -> negate(T2);
difference(T1, empty) -> T1;
difference(_T1, any) -> empty;
difference(#ty{
        dnf_ty_predefined = P1, dnf_ty_atom = A1, dnf_ty_interval = I1, 
        dnf_ty_list = L1, dnf_ty_bitstring = B1, ty_tuples = T1_1, 
        ty_functions = F1, dnf_ty_map = M1
    }, #ty{
        dnf_ty_predefined = P2, dnf_ty_atom = A2, dnf_ty_interval = I2, 
        dnf_ty_list = L2, dnf_ty_bitstring = B2, ty_tuples = T2_1, 
        ty_functions = F2, dnf_ty_map = M2
    }) ->
    
    simpl_to_repr(#ty{
        dnf_ty_predefined = dnf_ty_predefined:difference(P1, P2),
        dnf_ty_atom = dnf_ty_atom:difference(A1, A2),
        dnf_ty_interval = dnf_ty_interval:difference(I1, I2),
        dnf_ty_list = dnf_ty_list:difference(L1, L2),
        dnf_ty_bitstring = dnf_ty_bitstring:difference(B1, B2),
        ty_tuples = ty_tuples:difference(T1_1, T2_1),
        ty_functions = ty_functions:difference(F1, F2),
        dnf_ty_map = dnf_ty_map:difference(M1, M2)
    }).
% difference(T1, T2) ->
%   simpl_to_repr(binary_map(fun(Module, Left, Right) -> Module:difference(Left, Right) end, T1, T2)).

% TODO is there a better way to simplify edge cases?
-spec simpl_to_repr(type_record()) -> type().
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
  [{[T], [], _}] = ?assert_pattern([{[_], [], _}], dnf_ty_tuple:dnf(TupleDnf)),
  DnfMap = dnf_ty_map:singleton(T),
  map(DnfMap).

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables(any, _Cache) -> sets:new();
all_variables(empty, _Cache) -> sets:new();
all_variables(#ty{
    dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L,
    dnf_ty_bitstring = B, ty_tuples = T, ty_functions = F, dnf_ty_map = M
}, Cache) ->
    sets:union([
        dnf_ty_predefined:all_variables(P, Cache),
        dnf_ty_atom:all_variables(A, Cache),
        dnf_ty_interval:all_variables(I, Cache),
        dnf_ty_list:all_variables(L, Cache),
        dnf_ty_bitstring:all_variables(B, Cache),
        ty_tuples:all_variables(T, Cache),
        ty_functions:all_variables(F, Cache),
        dnf_ty_map:all_variables(M, Cache)
    ]).
% all_variables(TyRec, Cache) ->
%   fold(fun
%         (Module, Value, Vars) -> 
%           sets:union(Vars, Module:all_variables(Value, Cache))
%       end, 
%       sets:new(),
%       TyRec).


% ===
% Tallying
% ===

% helper function to be used for maybe expressions
-spec merge({Sofs, ST}, Sofs, monomorphic_variables()) -> 
    {Sofs, ST}  | {ok, Sofs, ST}
      when Sofs :: set_of_constraint_sets(), ST :: normalize_cache().
merge({[], S}, _, _Fixed) -> {[], S}; 
merge({R, S}, R2, Fixed) -> 
    Meet = constraint_set:meet(R, R2, Fixed),
    {ok, Meet, S} .


-spec normalize(type(), monomorphic_variables(), ST) -> 
    {set_of_constraint_sets(), ST} when ST :: normalize_cache().
normalize(any, _Fixed, Cache) -> {[], Cache};
normalize(empty, _Fixed, Cache) -> {[[]], Cache};
normalize(#ty{
    dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L,
    dnf_ty_bitstring = B, ty_tuples = T, ty_functions = F, dnf_ty_map = M
}, Fixed, ST) ->
    maybe
        {ok, R0, S0} ?= merge(dnf_ty_predefined:normalize(P, Fixed, ST), [[]], Fixed),
        {ok, R1, S1} ?= merge(dnf_ty_atom:normalize(A, Fixed, S0), R0, Fixed),
        {ok, R2, S2} ?= merge(dnf_ty_interval:normalize(I, Fixed, S1), R1, Fixed),
        {ok, R3, S3} ?= merge(dnf_ty_list:normalize(L, Fixed, S2), R2, Fixed),
        {ok, R4, S4} ?= merge(dnf_ty_bitstring:normalize(B, Fixed, S3), R3, Fixed),
        {ok, R5, S5} ?= merge(ty_tuples:normalize(T, Fixed, S4), R4, Fixed),
        {ok, R6, S6} ?= merge(ty_functions:normalize(F, Fixed, S5), R5, Fixed),
        {ok, R7, S7} ?= merge(dnf_ty_map:normalize(M, Fixed, S6), R6, Fixed),
        {R7, S7}
    end.
  % fold(fun
  %       (_, _, {[], LC0}) -> {[], LC0};
  %       (Module, Value, {ConstrsCurrent, LC0}) -> 
  %         {Normalized, LC1} = Module:normalize(Value, Fixed, LC0),
  %         {constraint_set:meet(ConstrsCurrent, Normalized, Fixed), LC1}
  %     end, 
  %     {[[]], ST},
  %     TyRec).

% ===
% Unparse
% ===

-spec unparse(type(), ST) -> {ast_ty(), ST} when ST :: unparse_cache().
unparse(T, ST) ->
  {Positive, ST0_A} = unparse_h(T, ST),
  {Negative, ST0_B} = unparse_h(negate(T), ST),

  case size(term_to_binary(Positive)) < size(term_to_binary(Negative)) of
    true -> {Positive, ST0_A};
    false -> {{negation, Negative}, ST0_B}
  end.

-spec unparse_h(type(), ST) -> {ast_ty(), ST} when ST :: unparse_cache().
unparse_h(any, Cache) -> {{predef, any}, Cache};
unparse_h(empty, Cache) -> {{predef, none}, Cache};
unparse_h(#ty{
        dnf_ty_predefined = P, dnf_ty_atom = A, dnf_ty_interval = I, dnf_ty_list = L,
        dnf_ty_bitstring = B, ty_tuples = T, ty_functions = F, dnf_ty_map = M
    }, ST) ->
    {P1, ST1} = dnf_ty_predefined:unparse(P, ST),
    Acc1 = unparse_any(dnf_ty_predefined:has_negative_only_line(P), dnf_ty_predefined, P1),
    
    {P2, ST2} = dnf_ty_atom:unparse(A, ST1),
    Acc2 = unparse_any(dnf_ty_atom:has_negative_only_line(A), dnf_ty_atom, P2),
    
    {P3, ST3} = dnf_ty_interval:unparse(I, ST2),
    Acc3 = unparse_any(dnf_ty_interval:has_negative_only_line(I), dnf_ty_interval, P3),
    
    {P4, ST4} = dnf_ty_list:unparse(L, ST3),
    Acc4 = unparse_any(dnf_ty_list:has_negative_only_line(L), dnf_ty_list, P4),
    
    {P5, ST5} = dnf_ty_bitstring:unparse(B, ST4),
    Acc5 = unparse_any(dnf_ty_bitstring:has_negative_only_line(B), dnf_ty_bitstring, P5),
    
    {P6, ST6} = ty_tuples:unparse(T, ST5),
    Acc6 = unparse_any(ty_tuples:has_negative_only_line(T), ty_tuples, P6),
    
    {P7, ST7} = ty_functions:unparse(F, ST6),
    Acc7 = unparse_any(ty_functions:has_negative_only_line(F), ty_functions, P7),
    
    {P8, ST8} = dnf_ty_map:unparse(M, ST7),
    Acc8 = unparse_any(dnf_ty_map:has_negative_only_line(M), dnf_ty_map, P8),
    
    Combined = [Acc1, Acc2, Acc3, Acc4, Acc5, Acc6, Acc7, Acc8],
    {ast_lib:mk_union(Combined), ST8}.
% unparse_h(Ty, ST) ->
%   {Z, ST2} = 
%   fold(fun 
%          (Module, Value, {Acc, ST0}) -> 
%            {P, ST1} = Module:unparse(Value, ST0), 
%            {Acc ++ [unparse_any(Module:has_negative_only_line(Value), Module, P)], ST1}
%        end, 
%        {[], ST}, 
%        Ty),
%   {ast_lib:mk_union(Z), ST2}.

-spec unparse_any(boolean(), type_module(), ast_ty()) -> ast_ty().
unparse_any(_, _, {predef, none}) -> {predef, none};
unparse_any(false, dnf_ty_predefined, Result) -> Result;
unparse_any(false, _, Result) when Result /= {predef, any} -> Result;
unparse_any(_, Module, Result) -> unparse_any_module(Module, Result).

-spec unparse_any_module(type_module(), ast_ty()) -> ast_ty().
unparse_any_module(dnf_ty_predefined, {predef, any}) -> {union, [{empty_list}, {empty_bitstring}, {predef, float}, {predef, pid}, {predef, port}, {predef, reference}]};
unparse_any_module(dnf_ty_predefined, Result) -> Result;
unparse_any_module(dnf_ty_atom, {predef, any}) -> {predef, atom};
unparse_any_module(dnf_ty_atom, Result) -> ast_lib:mk_intersection([{predef, atom}, Result]);
unparse_any_module(dnf_ty_interval, {predef, any}) -> {predef, integer};
unparse_any_module(dnf_ty_interval, Result) -> ast_lib:mk_intersection([{predef, integer}, Result]);
unparse_any_module(dnf_ty_list, {predef, any}) -> {improper_list, {predef, any}, {predef, any}};
unparse_any_module(dnf_ty_list, Result) -> ast_lib:mk_intersection([{improper_list, {predef, any}, {predef, any}}, Result]);
unparse_any_module(dnf_ty_bitstring, {predef, any}) -> {bitstring_cons, {predef, any}, {predef, any}};
unparse_any_module(dnf_ty_bitstring, Result) -> ast_lib:mk_intersection([{bitstring_cons, {predef, any}, {predef, any}}, Result]);
unparse_any_module(ty_tuples, {predef, any}) -> {tuple_any};
unparse_any_module(ty_tuples, Result) -> ast_lib:mk_intersection([{tuple_any}, Result]);
unparse_any_module(ty_functions, Result) -> ast_lib:mk_intersection([{fun_simple}, Result]);
unparse_any_module(dnf_ty_map, {predef, any}) -> {map_any};
unparse_any_module(dnf_ty_map, Result) -> ast_lib:mk_intersection([{map_any}, Result]).
% unparse_any(_, Module, _) -> 
%   error({no_unparse_implemented, Module}).


% record helper functions

% these helper function assume a fixed order for records in Erlang
% with the first index being the record name
% -spec map(fun((Module :: type_module(), Value) -> Value), type()) -> type(). % when Value :: Module:type()
% map(Map, Record) ->
%   Fields = record_info(fields, ty),
%   lists:foldl(
%     fun({Index, Field}, Rec) -> 
%       OldValue = element(Index, Record),
%       setelement(Index, Rec, Map(Field, OldValue))
%     end, 
%     Record, 
%     lists:zip(lists:seq(2, length(Fields) + 1), Fields)
%   ).

% same as map, but mapping over two records at once
% -spec binary_map(fun((Module :: type_module(), Value, Value) -> Value), type(), type()) -> type(). % when Value :: Module:type()
% binary_map(BinaryMap, Record1, Record2) ->
%   Fields = record_info(fields, ty),
%   lists:foldl(
%     fun({Index, Field}, Rec) -> 
%       OldLeftValue = element(Index, Record1),
%       OldRightValue = element(Index, Record2),
%       setelement(Index, Rec, BinaryMap(Field, OldLeftValue, OldRightValue))
%     end, 
%     Record1, 
%     lists:zip(lists:seq(2, length(Fields) + 1), Fields)
%   ).

% -spec fold(fun((Module :: type_module(), Value, Acc) -> Value), Acc, type()) -> Acc. % when Value :: Module:type()
% fold(Fold, BaseAcc, Record) ->
%   Fields = record_info(fields, ty),
%   lists:foldl(
%     fun({Index, Field}, Acc) -> 
%       Fold(Field, element(Index, Record), Acc)
%     end, 
%     BaseAcc, 
%     lists:zip(lists:seq(2, length(Fields) + 1), Fields)
%   ).

% -spec binary_fold(fun((Module :: type_module(), Value, Value, Acc) -> Value), Acc, type(), type()) -> Acc. % when Value :: Module:type()
% binary_fold(BinaryFold, BaseAcc, Record1, Record2) ->
%   Fields = record_info(fields, ty),
%   lists:foldl(
%     fun({Index, Field}, Acc) -> 
%       BinaryFold(Field, element(Index, Record1), element(Index, Record2), Acc)
%     end, 
%     BaseAcc, 
%     lists:zip(lists:seq(2, length(Fields) + 1), Fields)
%   ).
