-module(subtype_axioms_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).

a(A, B) -> tfun_full([A], B).
b(A) -> tatom(A).
n(A) -> tnegate(A).
u(A,B) -> tunion([A,B]).
i(A,B) -> tintersect([A,B]).
v(A) -> tvar(A).
p(A, B) -> ttuple([A, B]).

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