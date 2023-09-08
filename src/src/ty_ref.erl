-module(ty_ref).
-vsn({2,0,0}).

-export([any/0, store/1, load/1, new_ty_ref/0, define_ty_ref/2, is_empty_cached/1, store_is_empty_cached/2, store_recursive_variable/2, check_recursive_variable/1]).
-export([memoize/1, is_empty_memoized/1, reset/0, is_normalized_memoized/3]).

-on_load(setup_ets/0).
-define(TY_UTIL, ty_counter).        % counter store
-define(TY_MEMORY, ty_mem).          % id -> ty
-define(TY_UNIQUE_TABLE, ty_unique). % ty -> id

-define(EMPTY_MEMO, memoize_ty_ets).                            % ty_ref -> true

-define(EMPTY_CACHE, is_empty_memoize_ets). % ty_rec -> true/false

% helper table to construct recursive definitions properly
% once a bound variable is encountered in ty_rec:variable,
% it is treated as a recursive bound variable instead of a free one
-define(RECURSIVE_TABLE, remember_recursive_variables_ets).

all_tables() ->
  [?TY_UNIQUE_TABLE, ?TY_MEMORY, ?TY_UTIL, ?EMPTY_MEMO, ?EMPTY_CACHE, ?RECURSIVE_TABLE].

reset() ->
  ets:delete(?EMPTY_MEMO),
  ets:delete(?EMPTY_CACHE),

  ets:new(?EMPTY_CACHE, [public, named_table]),
  ets:new(?EMPTY_MEMO, [public, named_table]),

  % memoize ANY as not empty
  {ty_ref, AnyId} = ty_rec:any(),
  ets:insert(?EMPTY_CACHE, {AnyId, false}),

  % memoize EMPTY as empty
  {ty_ref, EmptyId} = ty_rec:empty(),
  ets:insert(?EMPTY_CACHE, {EmptyId, true})
.

-spec setup_ets() -> ok.
setup_ets() ->
  spawn(fun() ->
    % spawns a new process that is the owner of the variable id ETS table
    lists:foreach(fun(Tab) -> ets:new(Tab, [public, named_table]) end, all_tables()),
    ets:insert(?TY_UTIL, {ty_number, 0}),

    % define ANY node once
    ok = define_any(),

    % memoize ANY as not empty
    {ty_ref, AnyId} = ty_rec:any(),
    ets:insert(?EMPTY_CACHE, {AnyId, false}),

    % memoize EMPTY as empty
    {ty_ref, EmptyId} = ty_rec:empty(),
    ets:insert(?EMPTY_CACHE, {EmptyId, true}),

    receive _ -> ok end
        end),
  ok.

any() -> {ty_ref, 0}.

define_any() ->
  Any = {ty_ref, 0},

  % union
  Ty1 = dnf_var_ty_atom:any(),
  Ty2 = dnf_var_int:any(),
  Ty3 = {dnf_var_ty_tuple:any(), #{}},
  Ty4 = dnf_var_ty_function:any(),

  Ty = ty_rec:ty_of(Ty1, Ty2, Ty3, Ty4),

  % define
  ty_ref:define_ty_ref(Any, Ty),

  ok.

next_ty_id() ->
	ets:update_counter(?TY_UTIL, ty_number, {2, 1}).

new_ty_ref() ->
  {ty_ref, next_ty_id()}.

define_ty_ref({ty_ref, Id}, Ty) ->
%%  io:format(user, "Store NEW: ~p :=~n~p~n", [Id, Ty]),

  % TODO
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
  Object = ets:lookup(?TY_UNIQUE_TABLE, Ty),
  case Object of
    [] -> ok;
    _ ->
      io:format(user, "Defining a new type even though unique table has the type already!~n~p~n", [Ty]),
      error({define_type_ref, should_not_happen, polluted_memory_table}),
      ok
  end,

  ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
  ets:insert(?TY_MEMORY, {Id, Ty}),
  {ty_ref, Id}.

load({ty_ref, Id}) ->
  %%  io:format(user, "LOOKUP ~p -> ~p ~n", [Id, Object]),
  [{Id, Ty}] = ets:lookup(?TY_MEMORY, Id),
  Ty.

%%store_rec(Ty, OldRef) ->


store(Ty) ->
  Object = ets:lookup(?TY_UNIQUE_TABLE, Ty),
  case Object of
    [] ->
      Id = ets:update_counter(?TY_UTIL, ty_number, {2, 1}),
%%      io:format(user, "Store: ~p :=~n~p~n", [Id, Ty]),
      ets:insert(?TY_UNIQUE_TABLE, {Ty, Id}),
      ets:insert(?TY_MEMORY, {Id, Ty}),
      {ty_ref, Id};
    [{_, Id}] ->
%%      io:format(user, "o", []),
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
