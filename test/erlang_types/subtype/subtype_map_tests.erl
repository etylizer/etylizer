-module(subtype_map_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

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
  Any3 = i([Any1, Any2]),

  true = is_subtype(Empty, Any1),
  true = is_equiv(Any1, Any2),
  true = is_equiv(Any2, Any3),
  false = is_subtype(Any3, Empty),
  true = is_equiv(i([Any3, Empty]), Empty),
  ok.

maps_steps_test() ->
  Empty = tmap([]),
  AStep = tmap_field_opt(b(), tany()),
  IStep = tmap_field_opt(tint(), tany()),
  M1 = tmap([AStep]),
  M2 = tmap([IStep]),
  M3 = tmap([AStep, IStep]),
  M4 = tmap([AStep, IStep, tmap_field_opt(ttuple_any(), tempty())]),

  true = is_equiv(i([M1, M2]), Empty),
  true = is_equiv(i([M2, M3]), M2),
  true = is_equiv(M3, M4),
  ok.

maps_singletons_opt_test() ->
  % {1 := a, 2 => b, 10 => c}  !≤ ≥!  {1 => a, 2 := b, 3 => c}
  L = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_opt(tint(2), b(b)),
    tmap_field_opt(tint(10), b(c))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_opt(tint(2), b(b)),
    tmap_field_opt(tint(3), b(c))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),
  ok.

maps_singletons_mixed_test() ->
  % {1 := a, 2 => b, 10 => c}  !≤ ≥!  {1 => a, 2 := b, 3 => c}
  L = tmap([
    tmap_field_req(tint(1), b(a)),
    tmap_field_opt(tint(2), b(b)),
    tmap_field_opt(tint(10), b(c))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_req(tint(2), b(b)),
    tmap_field_opt(tint(3), b(c))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),
  ok.

maps_singletons_opt_2_test() ->
  % {1 => a, _ => none}  ≤ ≥!  {1 => a, 3 => a, _ => none} =:= {1|3 => a, _ => none}
  L = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_opt(tany(), tempty())
  ]),
  R = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_opt(tint(3), b(a)),
    tmap_field_opt(tany(), tempty())
  ]),
  R2 = tmap([
    tmap_field_opt(u([tint(1), tint(3)]), b(a)),
    tmap_field_opt(tany(), tempty())
  ]),
  true = is_subtype(L, R),
  false = is_subtype(R, L),
  true = is_equiv(R, R2),
  ok.

maps_singletons_mixed_2_test() ->
  % {1 := a, 2 => b}  !≤ ≥!  {1 => a, 2 := b}
  L = tmap([
    tmap_field_req(tint(1), b(a)),
    tmap_field_opt(tint(2), b(b))
  ]),
  R = tmap([
    tmap_field_opt(tint(1), b(a)),
    tmap_field_req(tint(2), b(b))
  ]),
  false = is_subtype(L, R),
  false = is_subtype(R, L),
  ok.

maps_precedence_1_test() ->
  % left-most match takes precedence
  % #{int() => int(), Any => foo} =:= {int() => int(), Any\int() => foo}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tany(), b(foo))
  ]),
  R = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(i([tany(), n(tint())]), b(foo))
  ]),
  true = is_subtype(L, R),
  true = is_subtype(R, L),
  ok.
