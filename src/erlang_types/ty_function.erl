-module(ty_function).

-ifndef(NODE).
-define(NODE, ty_node).
-endif.

-export([
  equal/2,
  compare/2,
  function/2,
  domain/1,
  codomain/1,
  unparse/2,
  all_variables/2
]).

-export_type([type/0]).
-type type() :: {ty_function, [?NODE:type()], ?NODE:type()}.
-type ast_ty() :: ast:ty().
-type all_variables_cache() :: ?NODE:all_variables_cache().
-type variable() :: ty_variable:type().

-spec compare(type(), type()) -> lt | gt | eq.
compare({ty_function, Domains1, Codomain1}, {ty_function, Domains2, Codomain2}) ->
  true = length(Domains1) =:= length(Domains2),
  utils:compare(
    fun(Node1, Node2) -> 
      ?NODE:compare(Node1, Node2) end,
    Domains1 ++ [Codomain1], 
    Domains2 ++ [Codomain2]
  ).

-spec equal(type(), type()) -> boolean().
equal(A, B) -> compare(A, B) == eq.

-spec function([N], N) -> type() when N :: ?NODE:type().
function(Refs, Ref2) when is_list(Refs) ->
  {ty_function, Refs, Ref2}.

% domain is returned as a type, not as a list of types!
-spec domain(type()) -> ?NODE:type().
domain({ty_function, Domains, _}) ->
  D = dnf_ty_variable:leaf(ty_rec:tuples(ty_tuples:singleton(length(Domains), dnf_ty_tuple:singleton(ty_tuple:tuple(Domains))))),
  ty_node:make(D).

-spec codomain(type()) -> ?NODE:type().
codomain({ty_function, _, Codomain}) when not is_list(Codomain) -> Codomain.

-spec unparse(type(), T) -> {ast_ty(), T}.
unparse({ty_function, Refs, Codomain}, ST0) ->
  {All, ST3} = lists:foldl(
                 fun(R, {Cs, ST1}) -> {C, ST2} = ty_node:unparse(R, ST1), {Cs ++ [C], ST2} end, 
                 {[], ST0}, 
                 Refs
                ),
  {Cod, ST4} = ty_node:unparse(Codomain, ST3),
  {{fun_full, All, Cod}, ST4}.

-spec all_variables(type(), all_variables_cache()) -> sets:set(variable()).
all_variables({ty_function, Domains, Codomain}, Cache) ->
  sets:union(
     [ty_node:all_variables(F, Cache) || F <- Domains]
  ++ [ty_node:all_variables(Codomain, Cache)]
  ).
