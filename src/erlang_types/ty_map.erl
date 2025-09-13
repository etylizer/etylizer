-module(ty_map).

-export([
  equal/2,
  compare/2,
  map/1,
  any/0,
  empty/0,
  components/1,
  big_intersect/1,
  unparse/2,
  all_variables/2
]).

-export_type([type/0]).

-ifndef(NODE).
-define(NODE, ty_node).
-endif.
%% union-of-tuple representation

-type type() :: {ty_map, _Ordered :: [ty_tuple:type()]}.
-type all_variables_cache() :: ?NODE:all_variables_cache().
-type ast_ty() :: ast:ty().

-spec compare(type(), type()) -> lt | gt | eq.
compare({ty_map, X}, {ty_map, Y}) ->
  utils:compare(fun ty_tuple:compare/2, X, Y).

-spec equal(type(), type()) -> boolean().
equal(A, B) -> compare(A, B) == eq.

-spec map(nonempty_list({N, N})) -> type() when N :: ?NODE:type().
map(Fields) ->
  Tuples = [ty_tuple:tuple([Ref1, Ref2]) || {Ref1, Ref2} <- Fields],
  OrderedTuples = lists:sort(fun(T1, T2) -> ty_tuple:compare(T1, T2) /= gt end, Tuples),
  {ty_map, OrderedTuples}.

-spec empty() -> type().
empty() -> map([{?NODE:any(), ?NODE:empty()}]).

-spec any() -> type().
any() -> map([{?NODE:any(), ?NODE:any()}]).

-spec components(type()) -> [ty_tuple:type()].
components({ty_map, X}) -> X.

-spec big_intersect(nonempty_list(type())) -> type().
big_intersect([M]) -> M;
big_intersect([{ty_map, X} | Ms]) ->
  XX = lists:foldr(fun({ty_map, Y}, Z) -> [[Tup | Tups] || Tup <- Y, Tups <- Z] end, [[T] || T <- X], Ms),
  BigX = [ty_tuple:big_intersect(Tups) || Tups <- XX],
  OrderedTuples = lists:sort(fun(T1, T2) -> ty_tuple:compare(T1, T2) /= gt end, BigX),
  {ty_map, OrderedTuples}.

-spec all_variables(type(), all_variables_cache()) -> _.
all_variables({ty_map, X}, Cache) ->
  sets:union(
    [ty_tuple:all_variables(Tup, Cache) || Tup <- X]
  ).

%-dialyzer(no_opaque).
-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({ty_map, X}, ST0) ->
  {AstTuples, ST1} = lists:foldr(fun(Tup, {Y, ST01}) -> {Ty, ST02} = ty_tuple:unparse(Tup, ST01), {[Ty | Y], ST02} end, {[], ST0}, X),
  AstMap = unparse_to_map(AstTuples),
  {AstMap, ST1}.

-spec unparse_to_map(nonempty_list(ast:ty_tuple())) -> ast:ty_map().
unparse_to_map([_ | _] = Tups) ->
  Existence = io_lib:format("~p", [{negation, {var, '⊥'}}]),
  F = fun
        ({tuple, [Key, Val]}, Acc) ->
          ValStr = io_lib:format("~p", [Val]),
          case string:find(ValStr, Existence) of
            nomatch ->
              [{map_field_opt, Key, Val} | Acc];
            _ ->
              [{map_field_req, Key, Val} | Acc]
          end
      end,
  AssocList = lists:foldr(F, [], Tups),
  {map, AssocList}.