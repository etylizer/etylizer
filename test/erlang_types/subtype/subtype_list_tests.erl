-module(subtype_list_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").


% list() < list()
list_01_test() ->
  T = tlist(tany()),
  true = is_subtype(T, T).

% [] < list()
% list() !< []
list_02_test() ->
  S = tempty_list(),
  T = tlist(tany()),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

% [a] < !> list()
list_03_test() ->
  S = tcons(b(a), tempty_list()),
  T = tlist(tany()),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

% [a, b] < !> list(atom)
list_04_test() ->
  S = tcons(b(a), tcons(b(b), tempty_list())),
  T = tlist(tatom()),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

% list(integer) < [1 | _] U [] U [integer() | _]
list_05_test() ->
  S = tlist(tint()),
  T = u([tcons(tint(1), tany()), tempty_list(), tcons(tint(), tany())]),
  true = is_subtype(S, T).

simple_list_test() ->
  S = tempty_list(),
  T = tlist(b(hello)),
  Ti = timproper_list(b(hello), tempty_list()),

  true = is_subtype(S, T),
  true = is_subtype(S, Ti),
  true = is_subtype(T, Ti).

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

