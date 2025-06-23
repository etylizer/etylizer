-module(representation_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

variable_test() ->
  global_state:with_new_state(fun() ->
    Ty = ty_parser:parse({var, alpha}),
    Tyy = ty_node:dump(Ty),
    #{{node, 1} := {node, _, {leaf, Any}, {leaf, Empty}}} = Tyy,
    gt = ty_rec:compare(Any, Empty),
    ok
  end).

% {leaf,0},#{1 => {leaf,0}} should simplify to {{leaf,0},#{}}
redundant_default_test() ->
  global_state:with_new_state(fun() ->
    Ty = ty_parser:parse(f([tany()], tany())),
    Ty2 = ty_node:negate(Ty),
    Ty3 = ty_node:intersect(Ty, Ty2),
    true = dnf_ty_variable:empty() =:= ty_node:load(Ty3)
  end).

% parser should map sub-structures of a recursive type to the same ID
% across parse passes
share_sub_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/system_rec"),
  with_symtab(fun() -> 
    Ty = ty_parser:parse(tnamed(ty)),
    Ty2 = ty_parser:parse(tnamed(ty_tuple)),
    true = Ty =:= ty_node:union(Ty, Ty2),
    ok
  end, System).

share_same_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/system_rec"),
  with_symtab(fun() -> 
    Ty = ty_parser:parse(tnamed(ty)),
    Ty2 = ty_parser:parse(u([tnamed(ty)])),
    true = Ty =:= Ty2,
    ok
  end, System).

% types parsed to the same structure should be shared
% across parse passes
share_simple_types_test() ->
  global_state:with_new_state(fun() ->
    Ty2 = ty_parser:parse(ttuple1(i([b(foo)]))),
    Ty2 = ty_parser:parse(ttuple1(b(foo))),
    ok
  end).

share_simple_types_2_test() ->
  global_state:with_new_state(fun() ->
    Ty = ttuple1(b(foo)),
    TyParsed = ty_parser:parse(Ty),

    Ty2 = ttuple1(u([b(foo)])),
    TyParsed = ty_parser:parse(Ty2),
    TyParsed = ty_parser:parse(Ty2),
    ok
  end).

share_topological_recursive_types_test() ->
  {ok, [System]} = file:consult("test_files/erlang_types/system_topological"),
  with_symtab(fun() ->
    Ty = {tuple, [
      {tuple, [{tuple, [{tuple, [{singleton, bar}, {singleton ,foo}]}]}]},
      {tuple, [{tuple, [{named, noloc, {ty_ref, '.', c, 0}, []}]}]},
      {named, noloc, {ty_ref, '.', e, 0}, []}
    ]},
    TyP = ty_parser:parse(Ty),

    Ty2 = {tuple, [ % root
      {intersection, [{tuple, [{tuple, [{tuple, [{singleton, bar}, {singleton ,foo}]}]}]}]}, %a %b % d, k
      {intersection, [{tuple, [{tuple, [{named, noloc, {ty_ref, '.', c, 0}, []}]}]}]}, % f, c
      {intersection, [{named, noloc, {ty_ref, '.', e, 0}, []}]} % e
    ]},
    TyP = ty_parser:parse(Ty2),
    ok
  end, System).

share_isomorphic_recursive_types_test() ->
  global_state:with_new_state(fun() ->
    % TODO test case with two isomorphic recursive types, and implement isomorphic detection
    ok
  end).
