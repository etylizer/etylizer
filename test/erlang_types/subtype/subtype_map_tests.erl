-module(subtype_map_tests).
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tyscm/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [is_subtype/2, is_equiv/2, named/2]).

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