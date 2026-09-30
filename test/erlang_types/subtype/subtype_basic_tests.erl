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

% fun((a) -> integer()) /\ fun((b1) -> any()) /\ .. /\ fun((bk) -> any()) 
% is a subtype of 
% fun((a) -> integer() | c)
%
% Every fun((bi) -> any()) will be dropped by phi.
% Its domain is disjoint from a, its codomain contains everything. 
%
% Branching on it instead leaves both branches with the same (T1, T2). 
%
% Only fun((a) -> integer()) covers the target, 
% and phi reaches it last. Every branch ends in true, nothing
% short-circuits, and the walk has 2^k leaves. 
% The target is not fun((a) -> integer()) itself, which the BDD would cancel against its
% negation without any search.
many_irrelevant_arrows_test_() ->
  {timeout, 30, fun() ->
    Arrow = f([b(a)], tint()),
    Others = [f([b(list_to_atom("phi_memo_b" ++ integer_to_list(I)))], tany()) || I <- lists:seq(1, 30)],
    Target = f([b(a)], u(tint(), b(c))),
    true = is_subtype(i([Arrow | Others]), Target),
    false = is_subtype(i(Others), Target)
  end}.
