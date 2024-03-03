-module(pretty_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tunion/1, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

% TODO simplifications
% the heuristic in gen_bdd:do_dnf already handles these cases, but it's only a heuristic
% S1: distribution over multiple coclauses
% not(mu5) /\ bool | not(mu6) /\ bool | mu6 /\ mu5 => bool | mu5 /\ mu6

empty_tuple_test() ->
  ecache:reset_all(),
  A = ast_lib:erlang_ty_to_ast(ast_lib:ast_to_erlang_ty(stdtypes:ttuple2(stdtypes:tint(), tnone()))),
  A = tnone(),
  ok.

any_empty_test() ->
  ecache:reset_all(),
  % syntactically same none and any representations
  A = stdtypes:tnone(),
  A = ast_lib:erlang_ty_to_ast(ast_lib:ast_to_erlang_ty(A)),

  B = stdtypes:tany(),
  B = ast_lib:erlang_ty_to_ast(ast_lib:ast_to_erlang_ty(B)),
  ok.

var_inter_test() ->
  ecache:reset_all(),
  A = tunion([
    tintersect([ tvar(mu5), tvar(mu6) ]),
    tintersect([ tnegate(tvar(mu6)), tatom(bool) ])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not(mu6) /\\ bool | mu5 /\\ bool | mu6 /\\ mu5", pretty:render_ty(Pretty)),
  ok.

var_inter2_test() ->
  ecache:reset_all(),
  A =
    tunion([
      tintersect([ tvar(mu5), tvar(mu6) ]),
      tintersect([ tnegate(tvar(mu6)), tatom(bool) ]),
      tintersect([ tnegate(tvar(mu5)), tatom(bool) ])
    ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("bool | mu6 /\\ mu5", pretty:render_ty(Pretty)),
  ok.

var_neg_dnf_test() ->
  ecache:reset_all(),
  A =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5)), (tatom(bool))]),
      tintersect([tnegate(tvar(mu5)), (tatom(bool))]),
      tintersect([tnegate(tvar(mu6)), (tatom(bool))]),
      tintersect([tvar(mu5), tnegate(tvar(mu6)), (tatom(bool))])
    ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not(mu6) /\\ bool | not(mu5) /\\ bool", pretty:render_ty(Pretty)),
  ok.

var_neg_inter_test() ->
  ecache:reset_all(),
  A =
    tnegate(tunion([
      tintersect([ tvar(mu5), tvar(mu6) ]),
      tintersect([ tnegate(tvar(mu6)), tatom(bool) ]),
      tintersect([ tnegate(tvar(mu5)), tatom(bool) ])
    ])),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not(bool | mu6 /\\ mu5)", pretty:render_ty(Pretty)),

  ok.

worth_negate_test() ->
  ecache:reset_all(),
  A = tnegate(tatom(a)) ,
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not(a)", pretty:render_ty(Pretty)),
  ok.

worth_negate2_test() ->
  ecache:reset_all(),
  A = tintersect([tnegate(tatom(a)), tnegate(tatom(b))]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not(a | b)", pretty:render_ty(Pretty)),
  ok.

ex1_test() ->
  ecache:reset_all(),
  A = {intersection, [
      {var,'$0'},
      {negation, {tuple,[{singleton,a}, {singleton, tag}]} },
      {tuple,[{singleton,b}, {singleton, tag}]}
    ]},
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("$0 /\\ {b, tag}", pretty:render_ty(Pretty)),

  ok.

variable_simple_union_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("a | b", pretty:render_ty(Pretty)),

  ok.

variable_union_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("foo | a", pretty:render_ty(Pretty)),
  ok.

variable_union2_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("foo | a | b", pretty:render_ty(Pretty)),
  ok.

variable_union3_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tvar(c), tatom(foo)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("foo | a | b | c", pretty:render_ty(Pretty)),
  ok.

variable_union4_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a),tatom()]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("atom() | a", pretty:render_ty(Pretty)),
  ok.

variable_union5_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a),tatom(), trange(2,4)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("atom() | 2..4 | a", pretty:render_ty(Pretty)),
  ok.

variable_union6_test() ->
  ecache:reset_all(),
  A = tunion([tvar(a), tvar(b), tvar(c), tvar(d), tatom(foo), trange(4,9)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("foo | 4..9 | a | b | c | d", pretty:render_ty(Pretty)),
  ok.

other_test() ->
  ecache:reset_all(),
  V0 = tunion([
    ttuple([tintersect([tatom(b), tvar(a5)]), tatom(int)]),
    ttuple([tatom(a), tatom(int)])
  ]),
  B = ast_lib:ast_to_erlang_ty(V0),
  Pretty = ast_lib:erlang_ty_to_ast(B),

  true = subty:is_equivalent(none, V0, Pretty),
  % TODO better simplification for variables, atom a is redundant in the intersection
  ?assertEqual("{a | a5 /\\ (a | b), int}", pretty:render_ty(Pretty)),
  % ?assertEqual("{a | a5 /\\ b, int}", pretty:render_ty(Pretty)),

  ok.

var_condition_test() ->
  ecache:reset_all(),
  A = tunion([
    tintersect([tnegate(tvar(a)), tvar(c)]),
    tintersect([tnegate(tvar(b)), tnegate(tvar(c))])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  % TODO better negations
  % not(c | b) | (c & not(a))

  ok.

tuple2_intersect_test() ->
  ecache:reset_all(),
  A = tintersect([
    ttuple([(tatom(a)), tatom(c)]),
    ttuple([(tatom()), (tatom(c))])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, c}", pretty:render_ty(Pretty)),

  ok.

tuple2_union_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([(tatom(a)), tatom(c)]),
    ttuple([(tatom()), (tatom(c))])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{atom(), c}", pretty:render_ty(Pretty)),

  ok.

tuple3_convert_test() ->
  ecache:reset_all(),
  A = ttuple([tatom(a), tatom(b), tatom(c)]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, b, c}", pretty:render_ty(Pretty)),
  ok.

tuple3_convert_neg_test() ->
  ecache:reset_all(),
  A = tnegate(ttuple([tatom(a), tatom(b), tatom(c)])),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not({a, b, c})", pretty:render_ty(Pretty)),
  ok.


tuple3_intersect_test() ->
  ecache:reset_all(),
  A = tintersect([
    ttuple([tatom(a), tatom(c), tatom(d)]),
    ttuple([tatom(), tatom(c), tatom()])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),

  ?assertEqual("{a, c, d}", pretty:render_ty(Pretty)),

  ok.

tuple3_union_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([tatom(a), tatom(c), tatom(d)]),
    ttuple([tatom(a), tatom(c), tatom(g)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, c, d | g}", pretty:render_ty(Pretty)),

  ok.

tuple3_union2_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([tatom(a), tatom(c), tatom(d)]),
    ttuple([tatom(a), tatom(g), tatom(d)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, c | g, d}", pretty:render_ty(Pretty)),

  ok.

tuple3_union3_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([tatom(a), tatom(c), tatom(d)]),
    ttuple([tatom(g), tatom(c), tatom(d)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a | g, c, d}", pretty:render_ty(Pretty)),

  ok.

tuple32_union_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([(tatom(a)), tatom(c), tatom(d)]),
    ttuple([(tatom(e)), (tatom(f)), tatom(g)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, c, d} | {e, f, g}", pretty:render_ty(Pretty)),

  ok.

tuple4_all_test() ->
  ecache:reset_all(),
  A = tintersect([tunion([
    ttuple([(tatom(a)), tatom(c), tatom(d), tatom()]),
    ttuple([(tatom(e)), (tatom(f)), tatom(g), tatom()])
  ]),
    ttuple([tany(), tatom(), tatom(), tatom(ra)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, c, d, ra} | {e, f, g, ra}", pretty:render_ty(Pretty)),

  ok.


tuple1_1_test() ->
  ecache:reset_all(),
  A = ttuple([tatom(a)]) ,
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a}", pretty:render_ty(Pretty)),

  ok.

tuple1_1_neg_test() ->
  ecache:reset_all(),
  A = tnegate(ttuple([tatom(a)])),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("not({a})", pretty:render_ty(Pretty)),

  ok.

tuple1_union_test() ->
  ecache:reset_all(),
  A = tunion([
    ttuple([tatom(a)]),
    ttuple([tatom(e)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a | e}", pretty:render_ty(Pretty)),

  ok.

tuple1_intersect_test() ->
  ecache:reset_all(),
  A = tintersect([
    ttuple([tatom(a)]),
    ttuple([tatom(e)])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("none()", pretty:render_ty(Pretty)),

  ok.

tuple1_intersect2_test() ->
  ecache:reset_all(),
  A = tintersect([
    ttuple([tunion([tatom(a), tatom(b)])]),
    ttuple([tatom(b)]),
    ttuple([tany()]),
    ttuple([tatom()])
  ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{b}", pretty:render_ty(Pretty)),

  ok.

tuple_pretty_test() ->
  ecache:reset_all(),
  V0 = tunion([
    ttuple([tintersect([tatom(b), tvar(a5)]), tatom(int)]), 
    ttuple([tatom(a), tatom(int)]),
    tintersect([
      tunion([
        ttuple([tintersect([tatom(b), tvar(a5)]), tatom(int)]),
        ttuple([tatom(a), tatom(int)])
      ]),
      tvar(a0a0)
    ])
  ]),
  A = tintersect([V0, ttuple([tatom(a), tatom(int)])]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{a, int}", pretty:render_ty(Pretty)),

  ok.

tuple_wrapped_test() ->
  ecache:reset_all(),

  A = ttuple([ ttuple([tany(), tany()]) ]),
  B = ast_lib:ast_to_erlang_ty(A),
  Pretty = ast_lib:erlang_ty_to_ast(B),
  true = subty:is_equivalent(none, A, Pretty),
  ?assertEqual("{{any(), any()}}", pretty:render_ty(Pretty)),

  ok.
