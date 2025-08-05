-module(subtype_basic_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").


atoms_test() ->
  S = b(hello),
  T = b(),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

empty_functions_test() ->
  AllFuns = f(),
  S = f([b(ok), tempty()], b(ok)),
  T = f([tempty(), b(hello), b(no)], b(ok2)),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  true = is_subtype(S, AllFuns),
  true = is_subtype(T, AllFuns).

intervals_test() ->
  [true = Result || Result <- [
    is_subtype(u([u([tint(), tint(1)]), tint(2)]), tint()),
    is_subtype(tint(1,2), tint()),
    is_subtype(tint(-254,299), tint()),
    is_subtype(tint(), tint()),
    is_subtype(tint(0), tint()),
    is_subtype(tint(0), tint()),
    is_subtype(tint(1), tint()),
    is_subtype(tint(-1), tint()),
    is_subtype(u([tint(1), tint(2)]), tint()),
    is_subtype(u([tint(-20,400), tint(300,405)]), tint()),
    is_subtype(i([u([tint(1), tint(2)]), tint(1,2)]), tint()),
    is_subtype(tint(2),  tint(1,2)),
    is_subtype(i([tint(), tint(2)]),  tint(1,2))
  ]].

intervals_not_test() ->
  [false = Result || Result <- [
    is_subtype(tint(), tint(1,2)),
    is_subtype(tint(1), tempty())
  ]].

intersection_test() ->
  S = a(u(b(a), b(b)), u(b(a), b(b))),
  T = a(u(b(a), b(b)), u(b(a), b(b))),
  true = is_subtype(S, T).

% annotation: 1|2 -> 1|2
% inferred body type: 1 -> 1 & 2 -> 2
refine_test() ->
  Annotation = a(u(b(a), b(b)), u(b(a), b(b))),
  Body = i(a(b(a), b(a)), a(b(b), b(b))),
  true = is_subtype(Body, Annotation),
  false = is_subtype(Annotation, Body).

edge_cases_test() ->
  false = is_subtype(v(alpha), tempty()),
  true = is_subtype(v(alpha), tany()),
  true = is_subtype(v(alpha), v(alpha)),
  false = is_subtype(v(alpha), v(beta)).

simple_var_test() ->
  S = v(alpha),
  T = b(int),
  A = tint(10, 20),

  false = is_subtype(S, A),
  false = is_subtype(S, T),
  false = is_subtype(A, S),
  false = is_subtype(T, S).

neg_var_fun_test() ->
  S = f([b(hello), v(alpha)], b(ok)),
  T = v(alpha),

  false = is_subtype(S, T),
  false = is_subtype(T, S).

pos_var_fun_test() ->
  S = i(f([b(hello)], b(ok)), v(alpha)),
  T = n(v(alpha)),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ).

simple_list_test() ->
  S = tempty_list(),
  T = tlist(b(hello)),
  Ti = timproper_list(b(hello), tempty_list()),

  true = is_subtype(S, T),
  false = is_subtype(S, Ti),
  false = is_subtype(T, Ti).

nonempty_list_test() ->
  S = tempty_list(),
  T = tnonempty_list(b(hello)),
  Ti = tnonempty_improper_list(b(hello), tempty_list()),

  false = is_subtype(S, T),
  false = is_subtype(S, Ti),
  true = is_subtype(T, Ti).

nonempty_list_2_test() ->
  Any = tany(),
  A = b(a),
  T1 = tnonempty_list(Any),
  T2 = u([tnonempty_list(A), tnonempty_list()]),
  true = is_equiv(T1, T2).

number_list_test() ->
  T = tlist(u([tint(), tfloat()])),
  S = tlist(tint()),

  true = is_subtype(S, T),
  false = is_subtype(T, S).

