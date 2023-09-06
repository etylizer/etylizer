-module(normalize_tests).
-include_lib("eunit/include/eunit.hrl").

-import(test_ast, [norm_substs/1, norm/1, mu/2, n/1, b/0, b/1, f/2, t/2, t/1, i/2, i/1, u/2, u/1, r/1, r/0, none/0, any/0, v/1, subty/2, normalize/3, normalize/2, var_of/1, norm_css/1]).

%%simple_empty_test() ->
%%  [[]] = normalize(v(alpha), any(), sets:new()),
%%  ok.
%%
%%simple_normalize_atom_test() ->
%%  % satisfiable constraint: some_atom <: ANY_atom
%%  [[]] = normalize(b(some_atom), b(), sets:new()),
%%
%%  % unsatisfiable constraint: ANY_atom <: some_atom
%%  [] = normalize(b(), b(some_atom), sets:new()),
%%
%%  Alpha = v(alpha),
%%  Beta = v(beta),
%%
%%  % simple variable constraints
%%  [] = normalize(Alpha, b(some_atom), sets:from_list([Alpha])),
%%  [] = normalize(Alpha, Beta, sets:from_list([Alpha, Beta])),
%%  [[]] = normalize(i(Alpha, b()), u(Beta, b()), sets:from_list([Alpha, Beta])),
%%
%%  ok.
%%
%%simple_atom_normalize_test() ->
%%  Alpha = v(alpha),
%%
%%  [[{V, L, R}]] = normalize(i(Alpha, b()), sets:new()),
%%  true = ty_rec:is_empty(L),
%%  true = ty_rec:is_equivalent(R, norm(n(b()))),
%%  V = var_of(Alpha),
%%
%%  ok.
%%
%%var_ordering_atom_normalize_test() ->
%%  Alpha = v(alpha),
%%  Beta = v(beta),
%%
%%  [[{V, L, R}]] = normalize(i([Beta, Alpha, b()]), sets:new()),
%%  true = ty_rec:is_empty(L),
%%  true = ty_rec:is_equivalent(R, norm(n(i(b(), Beta)))),
%%  V = var_of(Alpha),
%%
%%  ok.
%%
%%neg_var_atom_normalize_test() ->
%%  Alpha = v(alpha),
%%  Beta = v(beta),
%%
%%  [[{V, L, R}]] = normalize(i([Beta, n(Alpha), b()]), sets:new()),
%%  true = ty_rec:is_equivalent(ty_rec:any(), R),
%%  true = ty_rec:is_equivalent(L, norm(i(b(), Beta))),
%%  V = var_of(Alpha),
%%
%%  ok.
%%
%%simple_normalize_interval_test() ->
%%  [[]] = normalize(r(1), r(), sets:new()),
%%  [] = normalize(r(), r(1), sets:new()),
%%
%%  Alpha = v(alpha),
%%  Beta = v(beta),
%%
%%  % simple variable constraints
%%  [] = normalize(Alpha, r(1), sets:from_list([Alpha])),
%%  [] = normalize(Alpha, Beta, sets:from_list([Alpha, Beta])),
%%  [[]] = normalize(i(Alpha, r()), u(Beta, r()), sets:from_list([Alpha, Beta])),
%%
%%  ok.
%%
%%simple_normalize_tuple_test() ->
%%  [] = normalize(i(t(r(), r()), n(t(b(), b()))), sets:new()),
%%  [[]] = normalize(i(t(r(), r()), n(t(r(), r()))), sets:new()),
%%
%%  ok.
%%
%%example_1_normalize_test() ->
%%  % α→Bool ≤ β→β
%%  Result = normalize(f(v(alpha), b(bool)), f(v(beta), v(beta)), sets:new()),
%%
%%  % one valid solution (minimal)
%%  % { {(β≤0) (β≤α)}  {(bool≤β) (β≤α)} }
%%  Expected = norm_css([
%%    [{v(alpha), v(beta), any()}, {v(beta), none(), none()}],
%%    [{v(alpha), v(beta), any()}, {v(beta), b(bool), any()}]
%%  ]),
%%
%%  % paper solution (also minimal!)
%%  % { {(β≤0)}        {(bool≤β) (β≤α)} }
%%  Expected2 = norm_css([
%%    [{v(beta), none(), none()}],
%%    [{v(alpha), v(beta), any()}, {v(beta), b(bool), any()}]
%%  ]),
%%
%%  TestSubstitutions = norm_substs([
%%    #{v(alpha) => none(), v(beta) => any()},
%%    #{v(alpha) => any(), v(beta) => b(bool)}
%%  ]),
%%
%%  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),
%%  true = set_of_constraint_sets:is_equivalent(Expected2, Result, TestSubstitutions),
%%
%%  ok.
%%
%%
%%example_2_normalize_test() ->
%%  % (Int∨Bool → Int ≤ α → β)
%%  Result = normalize(f(u(r(), b(bool)), r()), f(v(alpha), v(beta)), sets:new()),
%%
%%  % solution
%%  % { {α≤0} , {α≤Int∨Bool, Int≤β} }
%%  Expected = norm_css([
%%    [{v(alpha), none(), none()}],
%%    [{v(alpha), none(), u(r(), b(bool))}, {v(beta), r(), any()}]
%%  ]),
%%
%%  TestSubstitutions = norm_substs([
%%    #{v(alpha) => none(), v(beta) => none()},
%%    #{v(alpha) => none(), v(beta) => any()},
%%    #{v(alpha) => none(), v(beta) => r()},
%%    #{v(alpha) => r(), v(beta) => r()}
%%  ]),
%%
%%  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),
%%
%%  ok.
%%
%%example_meet_normalize_test() ->
%%  % α→Bool ≤ β→β
%%  Res1 = normalize(f(v(alpha), b(bool)), f(v(beta), v(beta)), sets:new()),
%%  % Int∨Bool → Int ≤ α → β
%%  Res2 = normalize(f(u(r(), b(bool)), r()), f(v(alpha), v(beta)), sets:new()),
%%  % meet
%%  Result = constraint_set:merge_and_meet(Res1, Res2),
%%
%%  % expected minimal paper solution (2 & 3 constraint unsatisfiable)
%%  % { {α≤0, β≤0} {α≤Int∨Bool, Int≤β, β≤0} {Bool≤β, β≤α, α≤0} {α≤Int∨Bool, Int≤β, Bool≤β, β≤α} }
%%  Expected = norm_css([
%%    [{v(alpha), none(), none()}, {v(beta), none(), none()}],
%%    [{v(alpha), none(), u(r(), b(bool))}, {v(beta), r(), any()}, {v(beta), none(), none()}],
%%    [{v(alpha), none(), none()}, {v(alpha), v(beta), any()}, {v(beta), b(bool), any()}],
%%    [{v(alpha), none(), u(r(), b(bool))}, {v(alpha), v(beta), any()}, {v(beta), r(), any()}, {v(beta), b(bool), any()}]
%%  ]),
%%
%%  TestSubstitutions = norm_substs([
%%    #{v(alpha) => none(),  v(beta) => none()},
%%    #{v(alpha) => u(r(), b(bool)), v(beta) => u(r(), b(bool))}
%%  ]),
%%
%%  true = set_of_constraint_sets:is_equivalent(Expected, Result, TestSubstitutions),
%%
%%  ok.

test_1_test() ->
%%  {tintersect([tvar(zero), ttuple([])]), ttuple([])},
%%  {ttuple([]), tvar(zero)},
%%  {tvar(zero), ttuple([])},
%%  R1 = normalize(i(v(zero), t([])), t([])),
  R1 = normalize(v(zero), t([]), sets:new()),

  io:format(user, "R~p~n", [R1]),

  ok.