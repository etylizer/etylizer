-module(ty_ref).

-export([setup_ets/0, any/0, store/1, load/1, new_ty_ref/0, define_ty_ref/2, is_empty_cached/1, store_is_empty_cached/2, store_recursive_variable/2, check_recursive_variable/1]).
-export([memoize/1, is_empty_memoized/1, reset/0, is_normalized_memoized/3]).
-export([op_cache/3, memoize_norm/2, normalized_memoized/1, setup_all/0]).

-define(TY_UTIL, ty_counter).        % counter store
-define(TY_MEMORY, ty_mem).          % id -> ty
-define(TY_UNIQUE_TABLE, ty_unique). % ty -> id

-define(EMPTY_MEMO, memoize_ty_ets).                            % ty_ref -> true

-define(EMPTY_CACHE, is_empty_memoize_ets). % ty_rec -> true/false
-define(NORMALIZE_CACHE, normalize_cache_ets). % ty_ref -> SoCS

% helper table to construct recursive definitions properly
% once a bound variable is encountered in ty_rec:variable,
% it is treated as a recursive bound variable instead of a free one
-define(RECURSIVE_TABLE, remember_recursive_variables_ets).

op_cache(Op, K, Fun) ->
  case get({Op, K}) of
    undefined ->
      Res = Fun(),
      put({Op, K}, Res),
      Res;
    Z ->
      Z
  end.

all_tables() ->
  [?TY_UNIQUE_TABLE, ?TY_MEMORY, ?TY_UTIL, ?EMPTY_MEMO, ?EMPTY_CACHE, ?RECURSIVE_TABLE, ?NORMALIZE_CACHE].

reset() ->
  erase(),
  catch lists:foreach(fun(Tab) -> catch ets:delete(Tab) end, all_tables()),
  setup_all()
.

setup_all() ->
  % spawns a new process that is the owner of the variable id ETS table
  lists:foreach(fun(Tab) -> ets:new(Tab, [public, named_table]) end, all_tables()),
  ets:insert(?TY_UTIL, {ty_number, 0}),

  % define ANY node once
  ok = define_any(),

  % memoize ANY as not empty
  {ty_ref, AnyId} = ty_rec:any(),
  ets:insert(?EMPTY_CACHE, {AnyId, false}),
  ets:insert(?NORMALIZE_CACHE, {AnyId, []}),

  % memoize EMPTY as empty
  {ty_ref, EmptyId} = ty_rec:empty(),
  ets:insert(?EMPTY_CACHE, {EmptyId, true}),
  ets:insert(?NORMALIZE_CACHE, {EmptyId, [[]]}).

-spec setup_ets() -> ok.
setup_ets() ->
  setup_all(),
  ok.

any() -> {ty_ref, 0}.

define_any() ->
  Any = {ty_ref, 0},

  % union
  Ty0 = dnf_var_predef:any(),
  Ty1 = dnf_var_ty_atom:any(),
  Ty2 = dnf_var_int:any(),
  Tyl = dnf_var_ty_list:any(),
  Ty3 = {dnf_var_ty_tuple:any(), #{}},
  Ty4 = {dnf_var_ty_function:any(), #{}},
  Ty5 = dnf_var_ty_map:any(),

  Ty = ty_rec:ty_of(Ty0, Ty1, Ty2, Tyl, Ty3, Ty4, Ty5),

  % define
  ty_ref:define_ty_ref(Any, Ty),

  ok.

next_ty_id() ->
	ets:update_counter(?TY_UTIL, ty_number, {2, 1}).

new_ty_ref() ->
  NewEmptyRef = {ty_ref, (Id = next_ty_id())},

  % Insert empty only in memory, not in unique table
  ets:insert(?TY_MEMORY, {Id, ty_ref:load(ty_rec:empty())}),
  NewEmptyRef.

define_ty_ref({ty_ref, Id}, Ty) ->
  % when defining new (recursive) types manually,
  % the type to be built is already stored in the unique table
  % before finishing the manual definition
  % example: define_any stores the proper any type at the last ty_rec:union operation
  % after the union, that same type is stored again in the any reference
  % while the unique table still has one unique type to reference mapping,
  % the memory table gets polluted with duplicate types with different references
  % this became apparent when, in the last phase of tally,
  % one always defines the new recursive type without checking first if this is necessary
  % this creates a lot of {ty, 0, 0, 0, 0} (empty) types with (newly defined) different type references!
  % TODO think about this solution more thoroughly, edge cases?
  Object = ets:lookup(?TY_UNIQUE_TABLE, Ty),
  case Object of
    [] ->
      ok;
    [{_, _OldId}] ->
      % last ty ref inserted is the recursive type, delete from memory and decrease ty number by one
      % ets:delete(?TY_MEMORY, OldId),
      % [] = ets:lookup(?TY_MEMORY, OldId),
      % ets:update_counter(?TY_UTIL, ty_number, {2, -1}),
      ok
  end,

  % io:format(user, "Store (manual): ~p :=~n~p~n", [Id, Ty]),
  ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
  ets:insert(?TY_MEMORY, {Id, Ty}),
  {ty_ref, Id}.

load({ty_ref, Id}) ->
  [{Id, Ty}] = ets:lookup(?TY_MEMORY, Id),
  Ty.

%%store_rec(Ty, OldRef) ->


store(Ty) ->
  Object = ets:lookup(?TY_UNIQUE_TABLE, Ty),
  case Object of
    [] ->
      Id = ets:update_counter(?TY_UTIL, ty_number, {2, 1}),
      ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
      ets:insert(?TY_MEMORY, {Id, Ty}),
      % io:format(user, "Store: ~p :=~n~p~n", [Id, Ty]),
      {ty_ref, Id};
    [{_, Id}] ->
      {ty_ref, Id}
  end.

memoize({ty_ref, Id}) ->
  ets:insert(?EMPTY_MEMO, {Id, true}),
  ok.


is_empty_memoized({ty_ref, Id}) ->
  Object = ets:lookup(?EMPTY_MEMO, Id),
  case Object of
    [] -> miss;
    [{_, true}] -> true
  end.

memoize_norm({{ty_ref, Id}, Fixed}, Sol) ->
  ets:insert(?NORMALIZE_CACHE, {{Id, Fixed}, Sol}),
  ok.

normalized_memoized({{ty_ref, Id}, Fixed}) ->
  Object = ets:lookup(?NORMALIZE_CACHE, {Id, Fixed}),
  case Object of
    [] -> miss;
    [{_, Res}] -> Res
  end.

is_normalized_memoized(Id, _Fixed, M) ->
  Object = sets:is_element(Id, M),
  case Object of
    false -> miss;
    true -> true
  end.

is_empty_cached({ty_ref, Id}) ->
  Object = ets:lookup(?EMPTY_CACHE, Id),
  case Object of
    [] -> miss;
    [{_, Result}] ->
%%      io:format(user, "x", []),
      Result
  end.

store_is_empty_cached({ty_ref, Id}, Result) ->
  ets:insert(?EMPTY_CACHE, {Id, Result}),
  Result.

store_recursive_variable(Variable, Ty) ->
  ets:insert(?RECURSIVE_TABLE, {Variable, Ty}),
  ok.

check_recursive_variable(Variable) ->
  Object = ets:lookup(?RECURSIVE_TABLE, Variable),
  case Object of
    [] -> miss;
    [{_, Result}] -> Result
  end.
