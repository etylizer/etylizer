-module(subtype_basic_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).

a(A, B) -> {fun_full, [A], B}.
b(A) -> stdtypes:tatom(A).
u(A,B) -> stdtypes:tunion([A,B]).
i(A,B) -> stdtypes:tintersect([A,B]).
v(A) -> stdtypes:tvar(A).


atoms_test() ->
  S = tatom(hello),
  T = tatom(),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

empty_functions_test() ->
  AllFuns = {fun_simple},
  S = {fun_full, [tatom(ok), {predef, none}], tatom(ok)},
  T = {fun_full, [{predef, none}, tatom(hello), tatom(no)], tatom(ok2)},
  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  true = is_subtype(S, AllFuns),
  true = is_subtype(T, AllFuns),
  ok.

simple_int_test() ->
  true = is_subtype(stdtypes:trange_any(), stdtypes:trange_any()).

intervals_test() ->
  [true = Result || Result <- [
    is_subtype(tunion([tunion([trange_any(), trange(1,1)]), trange(2,2)]), trange_any()),
    is_subtype(trange(1,2), trange_any()),
    is_subtype(trange(-254,299), trange_any()),
    is_subtype(trange(0,0), trange_any()),
    is_subtype(trange(1,1), trange_any()),
    is_subtype(trange(-1,-1), trange_any()),
    is_subtype(tunion([trange(1,1), trange(2,2)]), trange_any()),
    is_subtype(tunion([trange(-20,400), trange(300,405)]), trange_any()),
    is_subtype(tintersect([tunion([trange(1,1), trange(2,2)]), trange(1,2)]), trange_any()),
    is_subtype(trange(2, 2),  trange(1,2)),
    is_subtype(tintersect([trange_any(), trange(2, 2)]),  trange(1,2))
  ]].

intervals_not_test() ->
  [false = Result || Result <- [ is_subtype(trange_any(),  trange(1,2)) ]].

interval_empty_test() ->
  [false = Result || Result <- [ is_subtype(trange(1,1),  {predef, none}) ]].

intersection_test() ->
  S = a(u(b(a), b(b)), u(b(a), b(b))),
  T = a(u(b(a), b(b)), u(b(a), b(b))),
  true = is_subtype( S, T ).

% annotation: 1|2 -> 1|2
% inferred body type: 1 -> 1 & 2 -> 2
refine_test() ->
  Annotation = a(u(b(a), b(b)), u(b(a), b(b))),
  Body = i(a(b(a), b(a)), a(b(b), b(b))),
  true = is_subtype( Body, Annotation ),
  false = is_subtype( Annotation, Body ).

edge_cases_test() ->
  false = is_subtype( v(alpha), {predef, none} ),
  true = is_subtype( v(alpha), {predef, any} ),
  true = is_subtype( v(alpha), v(alpha)),
  false = is_subtype( v(alpha), v(beta) ).

simple_var_test() ->
  S = v(alpha),
  T = b(int),
  A = stdtypes:trange(10, 20),

  false = is_subtype( S, A ),
  false = is_subtype( S, T ),
  false = is_subtype( A, S ),
  false = is_subtype( T, S ).

neg_var_fun_test() ->
  S = stdtypes:tfun_full([stdtypes:tatom(hello), stdtypes:tvar(alpha)], stdtypes:tatom(ok)),
  T = stdtypes:tvar(alpha),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

pos_var_fun_test() ->
  S = i(stdtypes:tfun_full([stdtypes:tatom(hello)], stdtypes:tatom(ok)), stdtypes:tvar(alpha)),
  T = stdtypes:tnegate(stdtypes:tvar(alpha)),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),

  ok.

simple_list_test() ->
  S = {empty_list},
  T = {list, {singleton, hello}},
  Ti = {improper_list, {singleton, hello}, {empty_list}},

  true = is_subtype(S, T),
  false = is_subtype(S, Ti),
  false = is_subtype(T, Ti).

nonempty_list_test() ->
  S = {empty_list},
  T = {nonempty_list, {singleton, hello}},
  Ti = {nonempty_improper_list, {singleton, hello}, {empty_list}},

  false = is_subtype(S, T),
  false = is_subtype(S, Ti),
  true = is_subtype(T, Ti).

nonempty_list_2_test() ->
  Any = stdtypes:any(),
  A = stdtypes:tatom(a),
  T1 = stdtypes:tnonempty_list(Any),
  T2 = ast_lib:mk_union([stdtypes:tnonempty_list(A), stdtypes:tnonempty_list()]),
  true = is_equiv(T1, T2).

number_list_test() ->
  T = {list, stdtypes:tunion([{predef, integer}, {predef, float}])},
  S = {list, stdtypes:tunion([{predef, integer}])},

  true = is_subtype(S, T),
  false = is_subtype(T, S).

simple_predef_alias_test() ->
  S = {predef_alias, term},
  true = is_subtype(S, S),
  ok.