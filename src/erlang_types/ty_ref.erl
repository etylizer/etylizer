-module(ty_ref).

-ifdef(TEST).
-export([write_dump_ty/1]).
-endif.

-export([
  setup_ets/0, any/0, store/1, load/1, new_ty_ref/0, define_ty_ref/2, 
  is_empty_cached/1, store_is_empty_cached/2, 
  normalize_cached/1, store_normalize_cached/2, 
  store_recursive_variable/2, 
  check_recursive_variable/1]).
-export([reset/0, is_normalized_memoized/3]).
-export([op_cache/3, memoize_norm/2, normalized_memoized/1, setup_all/0]).

-define(TY_UTIL, ty_counter).        % counter store
-define(TY_MEMORY, ty_mem).          % id -> ty
-define(TY_UNIQUE_TABLE, ty_unique). % ty -> id


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
  [?TY_UNIQUE_TABLE, ?TY_MEMORY, ?TY_UTIL, ?EMPTY_CACHE, ?RECURSIVE_TABLE, ?NORMALIZE_CACHE].

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
  Ty0 = dnf_var_ty_predef:any(),
  Ty1 = dnf_var_ty_atom:any(),
  Ty2 = dnf_var_ty_interval:any(),
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

normalize_cached(Id) ->
  Object = ets:lookup(?NORMALIZE_CACHE, Id),
  case Object of
    [] -> miss;
    [{_, Result}] ->
%%      io:format(user, "x", []),
      Result
  end.

store_normalize_cached(Id, Result) ->
  ets:insert(?NORMALIZE_CACHE, {Id, Result}),
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



-ifdef(TEST).

% very unstable, should only be used to generate proper test cases while debugging
-type dump() :: {{ty_ref, integer()}, integer(), #{{ty_ref, integer()} => Ty :: term()}}.
% % dump a type and all its dependencies for creating a test case via importing the state
-spec write_dump_ty({ty_ref, integer()}) -> dump().
write_dump_ty(Ty) ->
  State = lists:usort(write_dump_ty_h(Ty)),

  Ids = lists:usort(lists:flatten(utils:everything(
      fun F(InnerT) ->
          case InnerT of
              (Ref = {ty_ref, Id}) -> 
                TyRec = load(Ref),
                OtherIds = utils:everything(F, TyRec),
                {ok, [Id] ++ OtherIds};
              _ -> 
                error
          end
      end,
      Ty))),
  [MaxId | _] = lists:reverse(Ids),

  VarIds = lists:usort(lists:flatten(utils:everything(
      fun F(InnerT) ->
          case InnerT of
              (Ref = {ty_ref, Id}) -> 
                TyRec = load(Ref),
                OtherIds = utils:everything(F, TyRec),
                {ok, OtherIds};
              ({var, Id, Name}) when is_integer(Id) -> 
                {ok, Id};
              _ -> 
                error
          end
      end,
      Ty))) ++ [no_vars],
  [MaxVarId | _] = lists:reverse(VarIds),
  {Ty, MaxId, MaxVarId, maps:from_list(State)}.
write_dump_ty_h(Ty) ->
  State = utils:everything(
      fun(InnerT) ->
          % The return value error means: check recursively, no error here
          case InnerT of
              (Ref = {ty_ref, _Id}) -> 
                TyRec = load(Ref),
                More = write_dump_ty_h(TyRec),
                {ok, [{Ref, TyRec}] ++ More};
              _ -> 
                error
          end
      end,
      Ty),
  lists:flatten(State).

% read_dump_ty(Id, VarId, Db) ->
%   maps:foreach(fun({ty_ref, Idd}, Ty) ->
%     ets:insert(?TY_UNIQUE_TABLE, {Ty, Idd}),
%     ets:insert(?TY_MEMORY, {Idd, Ty})
%   end, Db),
%   ty_variable:update_id(VarId),
% 	ets:update_counter(?TY_UTIL, ty_number, {2, Id}).
% -ifdef(TEST).
% -include_lib("eunit/include/eunit.hrl").
% dump_db_usage_test() ->
%   test_utils:reset_ets(),
%   % term generated by write_dump_ty/1
%   {ok, [{Type, Id, VarId, Db}]} = file:consult("test_files/ty_rec/ty.config"),
%   read_dump_ty(Id, VarId, Db),

%   io:format(user,"~p -> ~p~n", [Type, load(Type)]),
%   ast_lib:erlang_ty_to_ast(Type),
%   ok.
% -endif.A

-endif.