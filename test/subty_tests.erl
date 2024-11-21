-module(subty_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tdiff/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2]).

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

atoms_test() ->
  S = stdtypes:tatom(hello),
  T = stdtypes:tatom(),
  true = is_subtype(S, T),
  false = is_subtype(T, S).

simple_tuple_test() ->
  S = {tuple, [{singleton, a}, {singleton, b}]},
  T = {tuple, [{predef, any}, {predef, any}]},
  true = is_subtype( S, T ),
  false = is_subtype( T, S ).

simple_tuple2_test() ->
  S = {tuple, [{singleton, a}]},
  T = {tuple, [{predef, any}, {predef, any}]},
  false = is_subtype( S, T ),
  false = is_subtype( T, S ).

empty_tuple_test() ->
  O2 = {intersection,
    [
      {tuple, [{singleton,b}]},
      {tuple,[{singleton,a}]}
    ]},

  true = subty:is_empty(O2, none),

  ok.

simple_prod_var_test() ->
  S = stdtypes:ttuple([stdtypes:tatom(hello)]),
  T = stdtypes:ttuple([stdtypes:tvar(alpha)]),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.


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

% (S-->T)&(S-->U) <: S-->T&U
axiom_intersection_test() ->
  S = i(a(b(s), b(t)), a(b(s), b(u))),
  T = a(b(s), i(b(t), b(u))),
  true = is_subtype( S, T ).

% (S-->U)&(T-->U) <: S|T-->U
axiom_union_test() ->
  S = i(a(b(s), b(u)), a(b(t), b(u))),
  T = a(u(b(s), b(t)), b(u)),
  true = is_subtype( S, T ).

% (o1 | o2) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
axiom_unions_test() ->
  S = a(u(b(o1), b(o2)), u(b(t1), b(t2))),
  T = i(a(b(o1), u(b(t1), b(t2))), a(b(o2), u(b(t1), b(t2)))),
  true = is_subtype( S, T ),
  true = is_subtype( T, S ).

% (o1 | o2) --> (t)  <:> ( o1 -> t ) & ( o2 -> t )
axiom_unions_left_test() ->
  S = a(u(b(o1), b(o2)), b(t)),
  T = i(a(b(o1), b(t)), a(b(o2), b(t))),
  true = is_subtype( S, T ),
  true = is_subtype( T, S ).

% (o) --> (t1 | t2)  <:> ( o1 -> t1 | t2 ) & ( o2 -> t1 | t2 )
axiom_unions_right_test() ->
  S = a(u(b(o1), b(o2)), u(b(t1), b(t2))),
  T = i(a(b(o1), u(b(t1), b(t2))), a(b(o2), u(b(t1), b(t2)))),
  true = is_subtype( S, T ),
  true = is_subtype( T, S ).

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


% (α × t) ∧ α !≤ ((1 × 1) × t)
tricky_substitution_step_5_test() ->
  A = tintersect([ttuple([v(alpha), b(int)]), v(alpha)]),
  B = ttuple([ttuple([tany(), tany()]), b(int)]),
  false = is_subtype( A, B ).

% (α → γ) ∧ (β → γ) ∼ (α∨β) → γ
arrow_distribution_test() ->
  S = i(a(v(alpha), v(gamma)), a(v(beta), v(gamma))),
  T = a(u(v(alpha), v(beta)), v(gamma)),
  true = is_subtype( S, T ),
  true = is_subtype( T, S ).

% ((α∨β) × γ) ∼ (α×γ) ∨ (β×γ)
distributivity_test() ->
  S = p(u(v(alpha), v(beta)), v(gamma)),
  T = u(p(v(alpha), v(gamma)), p(v(beta), v(gamma))),
  true = is_subtype( S, T ),
  true = is_subtype( T, S ).

% (α×γ → δ1 ) ∧ (β×γ → δ2 ) ≤ ((α∨β) × γ) → δ1 ∨ δ2
intersection_of_domains_and_codomains_arrows_test() ->
  S = i(a(p(v(alpha), v(gamma)), v(delta1)), a(p(v(beta), v(gamma)), v(delta2))),
  T = a(p(u(v(alpha), v(beta)), v(gamma)), u(v(delta1), v(delta2))),
  true = is_subtype( S, T ),
  false = is_subtype( T, S ).

% α ∧ (α × t) ≤ α
type_variables_are_not_basic_types_test() ->
  S = i(v(alpha), p(v(alpha), b(int))),
  T = v(alpha),
  true = is_subtype( S, T ).

% 1 → 0 ≤ α → β ≤ 0 → 1
non_trivial_arrow_containment_test() ->
  A = a(tany(), tnone()),
  B = a(v(alpha), v(beta)),
  C = a(tnone(), tany()),
  true = is_subtype( A, B ),
  true = is_subtype( B, C ),
  true = is_subtype( A, C ),

  false = is_subtype( B, A ),
  false = is_subtype( C, B ),
  false = is_subtype( C, A ).

% 1 ≤ ((α ⇒ β) ⇒ α) ⇒ α
pierces_law_test() ->
  A = tany(),
  B = u(n( u(n(u(n(v(alpha)), v(beta))), v(alpha)) ), v(alpha)),
  true = is_subtype( A, B ).

% nil × α ≤! (nil × ¬nil) ∨ (α × nil)
stuttering_validity_test() ->
  A = p(b(nil), v(alpha)),
  B = u(p(b(nil), b(nil)), p(v(alpha), b(nil))),
  false = is_subtype( A, B ).

% α1 → β1 ≤ ((α1 ∧α2 )→(β1 ∧β2 )) ∨ ¬(α2 →(β2 ∧¬β1 ))
subtle_arrow_relation_test() ->
  S = a(v(alpha1), v(beta1)),
  T = u(a(i(v(alpha1), v(alpha2)), i(v(beta1), v(beta2))),
    n(a(v(alpha2), i(v(beta2), n(v(beta1)))))),
  true = is_subtype( S, T ).

var_prod_test() ->
  S = i(stdtypes:ttuple([stdtypes:tatom(hello)]), stdtypes:tvar(alpha)),
  T = stdtypes:tvar(alpha),

  true = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

neg_var_prod_test() ->
  S = stdtypes:ttuple([stdtypes:tatom(hello), stdtypes:tvar(alpha)]),
  T = stdtypes:tvar(alpha),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

pos_var_prod_test() ->
  S = i(stdtypes:ttuple([stdtypes:tatom(hello)]), stdtypes:tvar(alpha)),
  T = stdtypes:tnegate(stdtypes:tvar(alpha)),

  false = is_subtype( S, T ),
  false = is_subtype( T, S ),
  ok.

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

%%simple_named_test() ->
%%  Scheme = stdtypes:tyscm([a], stdtypes:tfun([stdtypes:tvar(a), stdtypes:tvar(a)], stdtypes:tatom(ok))),
%%  TyDef = {mynamed, Scheme},
%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%  Sym = symtab:extend_symtab([Form], symtab:empty()),
%%
%%  S = {named, noloc(), {ref, mynamed, 1}, [{predef, integer}]},
%%  T = {named, noloc(), {ref, mynamed, 1}, [stdtypes:tatom(ok)]},
%%
%%  false = subty:is_subty(Sym, S, T),
%%  false = subty:is_subty(Sym, T, S),
%%  ok.
%%
%%simple_named2_test() ->
%%  Scheme2 = stdtypes:tyscm([a], stdtypes:tatom(helloworld)),
%%  TyDef2 = {mynamed2, Scheme2},
%%  Form2 = {attribute, noloc(), type, transparent, TyDef2},
%%
%%  Scheme = stdtypes:tyscm([a], {named, noloc(), {ref, mynamed2, 1}, [{var, a}]}),
%%  TyDef = {mynamed, Scheme},
%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%
%%
%%  M = symtab:extend_symtab([Form], symtab:empty()),
%%  Sym = symtab:extend_symtab([Form2], M),
%%
%%  S = {named, noloc(), {ref, mynamed, 1}, [stdtypes:tatom(helloworld)]},
%%  T = stdtypes:tatom(helloworld),
%%
%%  true = subty:is_subty(Sym, S, T),
%%  ok.
%%
%%simple_recursive_test() ->
%%  Scheme = stdtypes:tyscm([a],
%%    stdtypes:tunion([stdtypes:tatom(emptylist), stdtypes:ttuple([stdtypes:tvar(a), {named, noloc(), {ref, mylist, 1}, [stdtypes:tvar(a)]}])])
%%  ),
%%  TyDef = {mylist, Scheme},
%%  Form = {attribute, noloc(), type, transparent, TyDef},
%%
%%  Sym = symtab:extend_symtab([Form], symtab:empty()),
%%
%%  S = named(mylist, [stdtypes:tatom(myints)]),
%%  T = stdtypes:tatom(helloworld),
%%
%%  false = subty:is_subty(Sym, S, T),
%%  ok.
%%
%%simple_basic_ulist_test() ->
%%  SymbolTable = predefSymbolicTable(),
%%
%%  S = named(ulist, [{predef, integer}]),
%%  T = named(ulist, [stdtypes:tatom(float)]),
%%
%%  true = subty:is_subty(SymbolTable, S, S),
%%  false = subty:is_subty(SymbolTable, S, T),
%%  false = subty:is_subty(SymbolTable, T, S),
%%
%%  ok.
%%
%%% µx.(α×(α×x)) ∨ nil  ≤ µx.(α×x)     ∨ nil
%%% µx.(α×x)     ∨ nil !≤ µx.(α×(α×x)) ∨ nil
%%even_lists_contained_in_lists_test() ->
%%  S = named(even_ulist, [tvar(alpha)]),
%%  T = named(ulist, [tvar(alpha)]),
%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%  ok.
%%
%%% µx.(α×(α×x)) ∨ (α×nil)  ≤ µx.(α×x)     ∨ nil
%%% µx.(α×x)     ∨ (α×nil) !≤ µx.(α×(α×x)) ∨ nil
%%uneven_lists_contained_in_lists_test() ->
%%  S = named(uneven_ulist, [tvar(alpha)]),
%%  T = named(ulist, [tvar(alpha)]),
%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%  ok.
%%
%%% µx.(α×x) ∨ nil ∼ (µx.(α×(α×x))∨nil) ∨ (µx.(α×(α×x))∨(α×nil))
%%uneven_even_lists_contained_in_lists_test() ->
%%  S = tunion([
%%    named(uneven_ulist, [tvar(alpha)]),
%%    named(even_ulist, [tvar(alpha)])
%%  ]),
%%  T = named(ulist, [tvar(alpha)]),
%%
%%  true  = subty:is_subty(predefSymbolicTable(), S, T),
%%  true = subty:is_subty(predefSymbolicTable(), T, S),
%%  ok.
%%
%%% (µx.(α×(α×x))∨nil) <!> (µx.(α×(α×x))∨(α×nil))
%%uneven_even_lists_not_comparable_test() ->
%%  S = named(uneven_ulist, [tvar(alpha)]),
%%  T = named(even_ulist, [tvar(alpha)]),
%%
%%  false  = subty:is_subty(predefSymbolicTable(), S, T),
%%  false = subty:is_subty(predefSymbolicTable(), T, S),
%%  ok.
%%
%%
empty_tuples_edge_cases_test() ->
  S = stdtypes:ttuple([]),
  T = stdtypes:ttuple([stdtypes:tany()]),
  true = is_subtype(S, S),
  false = is_subtype(S, T),
  false = is_subtype(T, S),
  true = is_subtype(S, stdtypes:ttuple_any()),
  false = is_subtype(stdtypes:ttuple_any(), S),
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
%%
%%
%%
%%noloc() -> {loc, "no", 0, 0}.
%%named(Ref, Args) ->
%%  {named, noloc(), {ref, Ref, length(Args)}, Args}.
%%
%%
%%predefSymbolicTable() ->
%%  Scheme = stdtypes:tyscm([a],
%%    tunion([
%%      tatom('[]'),
%%      ttuple([tvar(a), named(ulist, [tvar(a)])])
%%    ])
%%  ),
%%  List = {attribute, noloc(), type, transparent, {ulist, Scheme}},
%%
%%  UnevenScheme = stdtypes:tyscm([a],
%%    tunion([
%%      ttuple([tvar(a), tatom('[]')]),
%%      ttuple([tvar(a), ttuple([tvar(a), named(uneven_ulist, [tvar(a)])])])
%%    ])
%%  ),
%%  UnevenList = {attribute, noloc(), type, transparent, {uneven_ulist, UnevenScheme}},
%%
%%  EvenScheme = stdtypes:tyscm([a],
%%    tunion([
%%      tatom('[]'),
%%      ttuple([tvar(a), ttuple([tvar(a), named(even_ulist, [tvar(a)])])])
%%    ])
%%  ),
%%  EvenList = {attribute, noloc(), type, transparent, {even_ulist, EvenScheme}},
%%
%%  % user-defined list :: µx.(α×x) ∨ nil
%%  % user-defined even list :: µx.(α×(α×x)) ∨ nil
%%  % user-defined uneven list :: µx.(α×(α×x)) ∨ (α×nil)
%%  symtab:extend_symtab([List, EvenList, UnevenList], symtab:empty()).


a(A, B) -> {fun_full, [A], B}.
b(A) -> stdtypes:tatom(A).
n(A) -> stdtypes:tnegate(A).
u(A,B) -> stdtypes:tunion([A,B]).
i(A,B) -> stdtypes:tintersect([A,B]).
v(A) -> stdtypes:tvar(A).
p(A, B) -> ttuple([A, B]).


bug1_test() ->
  O = {intersection,
    [{union,
         [{intersection,
              [{negation,{tuple,[{singleton,a}]}},
               {tuple,
                   [{intersection,
                        [{intersection,
                             [{negation,{singleton,a}},{singleton,b}]},
                         {union,
                             [{intersection,
                                  [{negation,{singleton,a}},{singleton,b}]},
                              {intersection,
                                  [{singleton,a},{singleton,b}]}]}]}]}]},
          {tuple,
              [{intersection,
                   [{intersection,[{singleton,a},{singleton,b}]},
                    {union,
                        [{intersection,
                             [{negation,{singleton,a}},{singleton,b}]},
                         {intersection,[{singleton,a},{singleton,b}]}]}]}]}]},
     {intersection,[{tuple,[{singleton,a}]},{tuple,[{predef,any}]}]}]},

  O2 = {intersection,
    [
      {tuple, [{singleton,b}]},
      {tuple,[{singleton,a}]}
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

% test cases for
% {S}          \ {T}          == {S \ T}
% {S1, S2}     \ {T1, T2}     == {S1 \ T1, S2}     U {S1, S2 \ T2}
% {S1, S2, S3} \ {T1, T2, T3} == {S1 \ T1, S2, S3} U {S1, S2 \ T2, S3} U {S1, S2, S3 \ T3}
% ... for any size
simplification_tuple_test() ->
  lists:foreach(fun(Size) ->
    A = fun(Prefix, T) -> list_to_atom(Prefix ++ integer_to_list(T)) end,
    Si = fun(I) -> [tvar(A("S",X)) || X <- lists:seq(1, I)] end,
    Ti = fun(I) -> [tvar(A("T",X)) || X <- lists:seq(1, I)] end,

    Sis = Si(Size),
    Tis = Ti(Size),

    TuplesLeftSide = tdiff(
      ttuple(Sis), 
      ttuple(Tis) 
    ),

    TuplesRightSide = tunion([ 
      ttuple([case Index of 
          I -> tdiff(lists:nth(Index, Sis), lists:nth(Index, Tis)); 
          _ -> lists:nth(Index, Sis) 
        end || Index <- lists:seq(1, Size)])
      || I <- lists:seq(1, length(Sis))]),

    true = is_equiv(TuplesLeftSide, TuplesRightSide)

  end, lists:seq(1, 5)).

% =====
% Map Tests
% =====

maps_any_empty_test() ->
  % #{}
  Empty = tmap([]),
  % map()
  Any1 = tmap_any(),
  % #{any() => any()}
  Any2 = tmap([tmap_field_opt(tany(), tany())]),
  Any3 = tintersect([Any1, Any2]),

  true = is_subtype(Empty, Any1),
  true = is_equiv(Any1, Any2),
  true = is_equiv(Any2, Any3),
  false = is_subtype(Any3, Empty),
  true = is_equiv(tintersect([Any3, Empty]), Empty),

  ok.

maps_steps_test() ->
  Empty = tmap([]),
  AStep = tmap_field_opt(tatom(), tany()),
  IStep = tmap_field_opt(tint(), tany()),
  M1 = tmap([AStep]),
  M2 = tmap([IStep]),
  M3 = tmap([AStep, IStep]),
  M4 = tmap([AStep, IStep, tmap_field_opt(ttuple_any(), tnone())]),

  true = is_equiv(tintersect([M1, M2]), Empty),
  true = is_equiv(tintersect([M2, M3]), M2),
  true = is_equiv(M3, M4),

  ok.

maps_singletons_opt_test() ->
  % {1 := a, 2 => b, 10 => c}  !≤ ≥!  {1 => a, 2 := b, 3 => c}
  L = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_opt(tint(2), tatom(b)),
    tmap_field_opt(tint(10), tatom(c))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_opt(tint(2), tatom(b)),
    tmap_field_opt(tint(3), tatom(c))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),

  ok.

maps_singletons_mixed_test() ->
  % {1 := a, 2 => b, 10 => c}  !≤ ≥!  {1 => a, 2 := b, 3 => c}
  L = tmap([
    tmap_field_req(tint(1), tatom(a)),
    tmap_field_opt(tint(2), tatom(b)),
    tmap_field_opt(tint(10), tatom(c))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_req(tint(2), tatom(b)),
    tmap_field_opt(tint(3), tatom(c))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),

  ok.

maps_singletons_opt_2_test() ->
  % {1 => a, _ => none}  ≤ ≥!  {1 => a, 3 => a, _ => none} =:= {1|3 => a, _ => none}
  L = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_opt(tany(), tnone())
  ]),
  R = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_opt(tint(3), tatom(a)),
    tmap_field_opt(tany(), tnone())
  ]),
  R2 = tmap([
    tmap_field_opt(tunion([tint(1), tint(3)]), tatom(a)),
    tmap_field_opt(tany(), tnone())
  ]),
  true = is_subtype(L, R),
  false = is_subtype(R, L),
  true = is_equiv(R, R2),

  ok.

maps_singletons_mixed_2_test() ->
  % {1 := a, 2 => b}  !≤ ≥!  {1 => a, 2 := b}
  L = tmap([
    tmap_field_req(tint(1), tatom(a)),
    tmap_field_opt(tint(2), tatom(b))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), tatom(a)),
    tmap_field_req(tint(2), tatom(b))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),

  ok.

maps_precedence_1_test() ->
  % left-most match takes precedence
  % #{int() => int(), Any => foo} =:= {int() => int(), Any\int() => foo}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tany(), tatom(foo))
  ]),
  R = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tintersect([tany(), tnegate(tint())]), tatom(foo))
  ]),

  true = is_subtype(L, R),
  true = is_subtype(R, L),

  ok.