-module(pretty_tests).
-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("etylizer/test/erlang_types/erlang_types_test_utils.hrl").

id(Type) ->
  Parsed = ty_parser:parse(Type),
  Unparsed = ty_parser:unparse(Parsed),
  Unparsed.

% TODO semantic pretty printing for tuples
% empty_tuple_test() ->
%   global_state:with_new_state(fun() -> 
%     A = ttuple([tint(), tnone()]),
%     A = id(A)
%   end).

any_empty_test() ->
  % syntactically same none and any representations
  global_state:with_new_state(fun() -> 
    A = tnone(),
    A = id(A)
  end),
  global_state:with_new_state(fun() -> 
    A = tany(),
    A = id(A)
  end).

simple_singleton_test() ->
  global_state:with_new_state(fun() -> 
    A = b(foo),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("foo", pretty:render_ty(B))
  end).

simple_singleton_negation_test() ->
  global_state:with_new_state(fun() -> 
    A = n(b(foo)),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("not(foo)", pretty:render_ty(B))
  end).

singleton_negation_test() ->
  global_state:with_new_state(fun() -> 
    A = i([n(b(a)), n(b(b))]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("not(a | b)", pretty:render_ty(B))
  end).

variable_union_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a), b(foo)]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("not(a) /\\ foo | a", pretty:render_ty(B)) % was "foo | a" before; need ty_rec factorization now
  end).

var_inter_test() ->
  global_state:with_new_state(fun() -> 
    A = u([
      i([ v(mu5), v(mu6) ]),
      i([ n(v(mu6)), b(bool) ])
    ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("mu5 /\\ mu6 | not(mu6) /\\ bool", pretty:render_ty(B))
  end).

var_inter2_test() ->
  global_state:with_new_state(fun() -> 
    A =
      u([
        i([ v(mu5), v(mu6) ]),
        i([ n(v(mu6)), b(bool) ]),
        i([ n(v(mu5)), b(bool) ])
      ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B), 
    % was "bool | mu6 /\\ mu5" before
    ?assertEqual("mu5 /\\ mu6 | not(mu5) /\\ bool | not(mu6) /\\ bool", pretty:render_ty(B))
  end).

var_neg_dnf_test() ->
  global_state:with_new_state(fun() -> 
    A =
      u([
        i([v(mu6), n(v(mu5)), (b(bool))]),
        i([n(v(mu5)), (b(bool))]),
        i([n(v(mu6)), (b(bool))]),
        i([v(mu5), n(v(mu6)), (b(bool))])
      ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("not(mu5) /\\ bool | not(mu6) /\\ bool", pretty:render_ty(B))
  end).

var_neg_inter_test() ->
  global_state:with_new_state(fun() -> 
    A =
      n(u([
        i([ v(mu5), v(mu6) ]),
        i([ n(v(mu6)), b(bool) ]),
        i([ n(v(mu5)), b(bool) ])
      ])),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    % was "not(bool | mu6 /\\ mu5)" before
    ?assertEqual("not(mu5) /\\ not(bool) | not(mu6) /\\ not(bool)", pretty:render_ty(B))
  end).

tuples_1_test() ->
  global_state:with_new_state(fun() -> 
    A = i([
      v('$0'),
      n(ttuple([b(a), b(tag)])),
      ttuple([b(b), b(tag)])
    ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("$0 /\\ {b, tag} /\\ not({a, tag})", pretty:render_ty(B))
  end).

variable_simple_union_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a), v(b)]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("a | b", pretty:render_ty(B))
  end).

variable_union_2_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a), v(b), b(foo)]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    % was "foo | a | b" before
    ?assertEqual("not(a) /\\ not(b) /\\ foo | a | b", pretty:render_ty(B))
  end).

variable_union_3_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a), v(b), v(c), b(foo)]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    % was "foo | a | b c" before
    ?assertEqual("not(a) /\\ not(b) /\\ not(c) /\\ foo | a | b | c", pretty:render_ty(B))
  end).

variable_union_4_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a),b()]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    % was "atom() | a" before
    ?assertEqual("not(a) /\\ atom() | a", pretty:render_ty(B))
  end).

variable_union_5_test() ->
  global_state:with_new_state(fun() -> 
    A = u([v(a),b(), tint(2,4)]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    % was "atom() | 2..4 | a"" before
    ?assertEqual("not(a) /\\ (atom() | 2..4) | a", pretty:render_ty(B))
  end).

other_test() ->
  global_state:with_new_state(fun() -> 
    A = u([
      ttuple([i([b(b), v(a5)]), b(int)]),
      ttuple([b(a), b(int)]),
      i([
        u([
          ttuple([i([b(b), v(a5)]), b(int)]),
          ttuple([b(a), b(int)])
        ]),
        v(a0a0)
      ])
    ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("{a, int} | {a5 /\\ b, int}", pretty:render_ty(B))
  end).

var_condition_test() ->
  global_state:with_new_state(fun() -> 
    A = u([
      i([n(v(a)), v(c)]),
      i([n(v(b)), n(v(c))])
    ]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("not(b) /\\ not(c) | c /\\ not(a)", pretty:render_ty(B))
  end).

recursive_test() ->
  global_state:with_new_state(fun() -> 
    X = tvar_mu(x),
    L = ttuple([X]),
    A = {mu, X, L},
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("mu $node_1.{mu $node_1}", pretty:render_ty(B))
  end).

recursive_2_test() ->
  global_state:with_new_state(fun() -> 
    X = tvar_mu(x),
    L = u([
      b(nil),
      ttuple([v(alpha), X])
    ]),
    A = {mu, X, L},
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("mu $node_1.nil | {alpha, mu $node_1}", pretty:render_ty(B))
  end).

empty_map_test() ->
  global_state:with_new_state(fun() -> 
    A = stdtypes:tmap([]),
    B = id(A),
    true = subty:is_equivalent(symtab:empty(), A, B),
    ?assertEqual("#{}", pretty:render_ty(B))
  end).

