-module(subtype_debug_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

% test cases that relate to an issue or 
% have been used for debugging purposes

foo2_branch1_test() ->
  % $0 /\ {a, 42}
  V0 = u([
    p(i(b(b), v(a5)), b(int)),
    p(b(a), b(int)),
    i([
      u([
        p(i(b(b), v(a5)), b(int)),
        p(b(a), b(int))
      ]),
      v(a0a0)
    ])
  ]),

  false = is_subtype(i([V0, p(b(a), b(int))]), tempty()),
  ok.

foo2_branch2_test() ->
  % $0 /\ !{a, 42} /\ {b, 42}
  V0 = u([
    p(i(b(b), v(a5)), b(int)),
    p(b(a), b(int)),
    i([
      u([
        p(i(b(b), v(a5)), b(int)),
        p(b(a), b(int))
      ]),
      v(a0a0)
    ])
  ]),

  false = is_subtype(i([
    V0,
    n(p(b(a), b(int))),
    p(b(b), b(int))
  ]), tempty()),
  ok.

bug1_test() ->
  O = i([
    u([
      i([
        n(p(b(a))),
        p(i([
          i([
            n(b(a)),
            b(b)
          ]),
          u([
            i([
              n(b(a)),
              b(b)
            ]),
            i([
              b(a),
              b(b)
            ])
          ])
        ]))
      ]),
      p(i([
        i([
          b(a),
          b(b)
        ]),
        u([
          i([
            n(b(a)),
            b(b)
          ]),
          i([
            b(a),
            b(b)
          ])
        ])
      ]))
    ]),
    i([
      p(b(a)),
      p(tany())
    ])
  ]),

  O2 = i([
    p(b(b)),
    p(b(a))
  ]),

  O3 = tempty(),

  true = is_equiv(O, O2),
  true = is_equiv(O2, O3),
  ok.

simplification_1_test() ->
  S = u([
    i([n(v(a5)), n(v(a6)), b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  T = u([
    i([n(v(a6)), b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_2_test() ->
  S = u([
    i([v(a5), v(a6)]),
    i([n(v(a5)), b(bool)]),
    i([n(v(a6)), b(bool)])
  ]),
  T = u([
    i([v(a5), v(a6)]),
    i([n(v(a5)), b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_3_test() ->
  S = u([
    i([v(a5), v(a6)]),
    i([n(v(a5)), b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  T = u([
    i([v(a5), v(a6)]),
    i([b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_4_test() ->
  S = u([
    i([v(a5), v(a6)]),
    i([b(bool)]),
    i([v(a5), n(v(a6)), b(bool)])
  ]),
  T = u([
    i([v(a5), v(a6)]),
    i([b(bool)])
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_5_test() ->
  S = u([
    i([v(a5), v(a6)]),
    i([n(v(a5)), b(bool)]),
    i([n(v(a6)), b(bool)])
  ]),
  T = u([
    i([v(a5), v(a6)]),
    b(bool)
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_6_test() ->
  S = u([
    i([v(mu5), v(mu6)]),
    i([n(v(mu6)), b(bool)]),
    i([n(v(mu5)), b(bool)])
  ]),
  true = is_subtype(S, n(n(S))),
  true = is_subtype(n(n(S)), S).

simplification_7_test() ->
  S = n(u([
    i([v(mu5), v(mu6)]),
    i([n(v(mu6)), b(bool)]),
    i([n(v(mu5)), b(bool)])
  ])),
  T = i([
    u([n(v(mu5)), n(v(mu6))]),
    u([v(mu6), n(b(bool))]),
    u([v(mu5), n(b(bool))])
  ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_8_test() ->
  % X ∩ (A∪B)=(X∩A)∪(X∩B)
  A = n(v(mu5)),
  B = n(v(mu6)),
  X = i([
    u([v(mu6), n(b(bool))]),
    u([v(mu5), n(b(bool))])
  ]),
  S = i([u([A, B]), X]),
  T = u([
    i([A, X]),
    i([B, X])
  ]),
  T2 = u([
    i([v(mu6), n(v(mu5)), n(b(bool))]),
    i([n(v(mu5)), n(b(bool))]),
    i([B, X])
  ]),
  T3 = u([
    i([v(mu6), n(v(mu5)), n(b(bool))]),
    i([n(v(mu5)), n(b(bool))]),
    i([B, u([
      i([v(mu6), v(mu5)]),
      i([v(mu5), n(b(bool))]),
      i([v(mu6), n(b(bool))]),
      n(b(bool))
    ])])
  ]),
  T4 = u([
    i([v(mu6), n(v(mu5)), n(b(bool))]),
    i([n(v(mu5)), n(b(bool))]),
    i([n(v(mu6)), n(b(bool))]),
    i([v(mu5), n(v(mu6)), n(b(bool))])
  ]),
  true = is_equiv(S, T),
  true = is_equiv(T, T2),
  true = is_equiv(T2, T3),
  true = is_equiv(T3, T4),
  ok.

simplification_9_test() ->
  % X ∩ (A∪B)=(X∩A)∪(X∩B)
  S = u([
    i([v(mu6), n(v(mu5)), b(bool)]),
    i([n(v(mu5)), b(bool)]),
    i([n(v(mu6)), b(bool)]),
    i([v(mu5), n(v(mu6)), b(bool)])
  ]),
  T = u([
    i([n(v(mu5)), b(bool)]),
    i([n(v(mu6)), b(bool)])
  ]),
  true = is_equiv(S, T),
  ok.

simplification_10_test() ->
  S = u([
    i([v(mu6), n(v(mu5))]),
    n(v(mu5)),
    n(v(mu6)),
    i([v(mu5), n(v(mu6))])
  ]),
  T = u([
    n(v(mu5)),
    n(v(mu6))
  ]),
  true = is_equiv(S, T),
  ok.

tally_09_expected_test() ->
  S = tint(1),
  T = u([ 
         i([tint(1), tint(), n(v(beta))]),
         i([v(beta), tint()])
        ]),
  true = is_subtype(S, T),
  ok.
