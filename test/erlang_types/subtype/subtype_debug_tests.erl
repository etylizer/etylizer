-module(subtype_debug_tests).
-include_lib("eunit/include/eunit.hrl").

% test cases that relate to an issue or 
% have been used for debugging purposes

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).

foo2_branch1_test() ->
  % $0 /\ {a, 42}
  % $0 :: (`b & 'a5,42)  | (`a,42) | ((`b & 'a5,42) | (`a,42)) & 'a0a0;
  % debug subtype ((((`b & 'a5,42)  | (`a,42) | ((`b & 'a5,42) | (`a,42)) & 'a0a0) & (`a, 42)) (Empty));;
  % (`a,42) <= Empty : false
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

  false = is_subtype(tintersect([V0, ttuple([tatom(a), tatom(int)])]), stdtypes:tnone()),
  ok.

foo2_branch2_test() ->
  % $0 /\ !{a, 42} /\ {b, 42}
  % $0 ::
  %   (`b & 'a5,42)
  % | (`a,42)
  % | ((`b & 'a5,42) | (`a,42)) & 'a0a0;
  % debug subtype ((((`b & 'a5,42)  | (`a,42) | ((`b & 'a5,42) | (`a,42)) & 'a0a0) & (`b, 42) \ (`a, 42)) (Empty));;
  % (`b & 'a5,42) <= Empty : false
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

  false = is_subtype(tintersect([
    V0,
    tnegate(ttuple([tatom(a), tatom(int)])),
    ttuple([tatom(b), tatom(int)])
  ]), stdtypes:tnone()),
  ok.

bug1_test() ->
  O = {intersection,
    [{union,
         [{intersection,
              [{negation,{tuple,[tatom(a)]}},
               {tuple,
                   [{intersection,
                        [{intersection,
                             [{negation,tatom(a)},tatom(b)]},
                         {union,
                             [{intersection,
                                  [{negation,tatom(a)},tatom(b)]},
                              {intersection,
                                  [tatom(a),tatom(b)]}]}]}]}]},
          {tuple,
              [{intersection,
                   [{intersection,[tatom(a),tatom(b)]},
                    {union,
                        [{intersection,
                             [{negation,tatom(a)},tatom(b)]},
                         {intersection,[tatom(a),tatom(b)]}]}]}]}]},
     {intersection,[{tuple,[tatom(a)]},{tuple,[{predef,any}]}]}]},

  O2 = {intersection,
    [
      {tuple, [tatom(b)]},
      {tuple,[tatom(a)]}
    ]},

  O3 = {predef, none},

  true = is_equiv(O, O2),
  true = is_equiv(O2, O3),

  ok.

simplification_1_test() ->
  S =
  tunion([
    tintersect([tnegate(tvar(a5)), tnegate(tvar(a6)), tatom(bool)]),
    tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
  ]),
  T =
    tunion([
      tintersect([tnegate(tvar(a6)), tatom(bool)]),
      tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
    ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_2_test() ->
  S =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tnegate(tvar(a5)), tatom(bool)]),
      tintersect([tnegate(tvar(a6)), tatom(bool)])
    ]),
  T =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tnegate(tvar(a5)), tatom(bool)]),
      tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
    ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_3_test() ->
  S =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tnegate(tvar(a5)), tatom(bool)]),
      tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
    ]),
  T =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tatom(bool)]),
      tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
    ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_4_test() ->
  S =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tatom(bool)]),
      tintersect([tvar(a5), tnegate(tvar(a6)), tatom(bool)])
    ]),
  T =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tatom(bool)])
    ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_5_test() ->
  S =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tintersect([tnegate(tvar(a5)), tatom(bool)]),
      tintersect([tnegate(tvar(a6)), tatom(bool)])
    ]),
  T =
    tunion([
      tintersect([(tvar(a5)), (tvar(a6))]),
      tatom(bool)
    ]),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_6_test() ->
  S =
    (tunion([
      tintersect([ tvar(mu5), tvar(mu6) ]),
      tintersect([ tnegate(tvar(mu6)), tatom(bool) ]),
      tintersect([ tnegate(tvar(mu5)), tatom(bool) ])
    ])),
  true = is_subtype(S, tnegate(tnegate(S))),
  true = is_subtype(tnegate(tnegate(S)), S).

simplification_7_test() ->
  S =
    tnegate(tunion([
      tintersect([ tvar(mu5), tvar(mu6) ]),
      tintersect([ tnegate(tvar(mu6)), tatom(bool) ]),
      tintersect([ tnegate(tvar(mu5)), tatom(bool) ])
    ])),
  T =
    (tintersect([
      (tunion([ tnegate(tvar(mu5)), tnegate(tvar(mu6)) ])),
      (tunion([ (tvar(mu6)), tnegate(tatom(bool)) ])),
      (tunion([ (tvar(mu5)), tnegate(tatom(bool)) ]))
    ])),
  true = is_subtype(S, T),
  true = is_subtype(T, S).

simplification_8_test() ->
  % X ∩ (A∪B)=(X∩A)∪(X∩B)
  S =
    (tintersect([
      (tunion([ A = tnegate(tvar(mu5)), B = tnegate(tvar(mu6)) ])),
      X = tintersect([
        (tunion([ (tvar(mu6)), tnegate(tatom(bool)) ])),
        (tunion([ (tvar(mu5)), tnegate(tatom(bool)) ]))
      ])
    ])),
  T =
  tunion([
    tintersect([A, X]),
    tintersect([B, X])
  ]),
  T2 =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([(B), X])
    ]),
  T3 =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([B, tunion([
        tintersect([tvar(mu6), tvar(mu5)]),
        tintersect([tvar(mu5), tnegate(tatom(bool))]),
        tintersect([tvar(mu6), tnegate(tatom(bool))]),
        tnegate(tatom(bool))
      ])])
    ]),
  T4 =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([tnegate(tvar(mu5)), tnegate(tatom(bool))]),
      tintersect([tnegate(tvar(mu6)), tnegate(tatom(bool))]),
      tintersect([tvar(mu5), tnegate(tvar(mu6)), tnegate(tatom(bool))])
    ]),

  true = is_equiv(S, T),
  true = is_equiv(T, T2),
  true = is_equiv(T2, T3),
  true = is_equiv(T3, T4),

  ok.

simplification_9_test() ->
  % X ∩ (A∪B)=(X∩A)∪(X∩B)
  S =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5)), (tatom(bool))]),
      tintersect([tnegate(tvar(mu5)), (tatom(bool))]),
      tintersect([tnegate(tvar(mu6)), (tatom(bool))]),
      tintersect([tvar(mu5), tnegate(tvar(mu6)), (tatom(bool))])
    ]),
  T =
    tunion([
      tintersect([tnegate(tvar(mu5)), (tatom(bool))]),
      tintersect([tnegate(tvar(mu6)), (tatom(bool))])
    ]),
  true = is_equiv(S, T),

  ok.

simplification_10_test() ->
  S =
    tunion([
      tintersect([tvar(mu6), tnegate(tvar(mu5))]),
      tnegate(tvar(mu5)),
      tnegate(tvar(mu6)),
      tintersect([tvar(mu5), tnegate(tvar(mu6))])
    ]),
  T =
    tunion([
      tnegate(tvar(mu5)),
      tnegate(tvar(mu6))
    ]),
  true = is_equiv(S, T),

  ok.