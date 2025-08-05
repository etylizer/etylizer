-module(ty_tuple).

-export([
  compare/2,
  equal/2,
  tuple/1,
  any/1,
  empty/1,
  all_variables/2,
  unparse/2,
  big_intersect/1,
  components/1
]).

-export_type([type/0]).

-ifndef(NODE).
-define(NODE, ty_node).
-endif.
%% n-tuple representation

-type type() :: {ty_tuple, non_neg_integer(), [?NODE:type()]}.
-type all_variables_cache() :: ?NODE:all_variables_cache().
-type ast_ty() :: ast:ty().

-spec compare(type(), type()) -> lt | gt | eq.
compare({ty_tuple, Dim, C}, {ty_tuple, Dim, C2}) ->
  utils:compare(fun ?NODE:compare/2, C, C2).

-spec equal(type(), type()) -> boolean().
equal(P1, P2) -> compare(P1, P2) =:= eq.

-spec tuple([N]) -> type() when N :: ?NODE:type().
tuple(Refs) -> {ty_tuple, length(Refs), Refs}.

-spec empty(non_neg_integer()) -> type().
empty(Size) -> {ty_tuple, Size, [?NODE:empty() || _ <- lists:seq(1, Size)]}.

-spec any(non_neg_integer()) -> type().
any(Size) -> {ty_tuple, Size, [?NODE:any() || _ <- lists:seq(1, Size)]}.

-spec components(type()) -> [?NODE:type()].
components({ty_tuple, _, Refs}) -> Refs.

-spec big_intersect(nonempty_list(type())) -> type().
big_intersect([X]) -> X;
big_intersect([X | Y]) ->
    lists:foldl(fun({ty_tuple, _, Refs}, {ty_tuple, Dim, Refs2}) ->
        true = length(Refs) == length(Refs2),
        {ty_tuple, Dim, [?NODE:intersect(S, T) || {S, T} <- lists:zip(Refs, Refs2)]}
                end, X, Y).

-spec all_variables(type(), all_variables_cache()) -> _.
all_variables({ty_tuple, _, Refs}, Cache) ->
  sets:union(
    [ty_node:all_variables(T, Cache) || T <- Refs]
  ).

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({ty_tuple, _, Refs}, ST0) ->
  {All, ST3} = lists:foldl(
                 fun(R, {Cs, ST1}) -> {C, ST2} = ty_node:unparse(R, ST1), {Cs ++ [C], ST2} end, 
                 {[], ST0}, 
                 Refs
                ),
  {{tuple, All}, ST3}.

