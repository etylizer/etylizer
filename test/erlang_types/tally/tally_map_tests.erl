-module(tally_map_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2
                  ]).


% =====
% Map Normalization
% =====
maps_norm_opt_1_test() ->
  % #{int() => int()} ⊏ #{a => β}
  L = tmap([tmap_field_opt(tint(), tint())]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_utils:test_tally([{L, R}],
    [{#{alpha => tint(), beta => tint()},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_2_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tatom(), tatom())
  ]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_utils:test_tally([{L, R}],
    [{#{alpha => tunion(tint(), tatom()), beta => tunion(tint(), tatom())},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_3_test() ->
  % #{int() => int(), _       => foo}  ≤  #{a => β}
  % #{int() => int(), _\int() => foo}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tany(), tatom(foo))
  ]),
  R = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),

  test_utils:test_tally([{L, R}],
    [{#{alpha => tany(), beta => tunion(tint(), tatom(foo))},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_4_test() ->
  % #{a => int()}  ≤  #{int() => β}
  L1 = tmap([tmap_field_opt(tvar(alpha), tint())]),
  R1 = tmap([tmap_field_opt(tint(), tvar(beta))]),
  test_utils:test_tally([{L1, R1}], test_utils:solutions(2)),

  % #{int() => β}  ≤  #{a => int()}
  L2 = tmap([tmap_field_opt(tint(), tvar(beta))]),
  R2 = tmap([tmap_field_opt(tvar(alpha), tint())]),

  test_utils:test_tally([{L2, R2}], test_utils:solutions(2)).

maps_norm_opt_5_test() ->
  % #{a => int(), _   => atom()}  ≤  #{β => atom() | int()}
  % #{a => int(), _\a => atom()}  ≤  #{β => atom() | int()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = tmap([
    tmap_field_opt(tvar(beta), tunion(tatom(), tint()))
  ]),

  test_utils:test_tally([{L, R}], test_utils:solutions(1)).

maps_norm_opt_6_test() ->
  % #{a => β} ≤ #{atom() => int()}
  L = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),
  R = tmap([tmap_field_opt(tatom(), tint())]),

  test_utils:test_tally([{L, R}], test_utils:solutions(3)).


maps_norm_opt_7_test() ->
  % #{a => atom()}  ≤  #{β => any()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tatom())
  ]),
  R = tmap([
    tmap_field_opt(tvar(beta), tany())
  ]),
  test_utils:test_tally([{L, R}], test_utils:solutions(1)).

maps_norm_opt_8_test() ->
  % #{}  ≤  #{a => β}
  L = tmap([]),
  R1 = tmap([tmap_field_opt(tvar(alpha), tvar(beta))]),
  test_utils:test_tally([{L, R1}], test_utils:solutions(1)),

  % #{}  ≤  #{a => β} /\ #{}
  R2 = tintersect([R1, L]),
  test_utils:test_tally([{L, R2}], test_utils:solutions(1)).

maps_norm_opt_9_test() ->
  % #{foo => int(), _     => any()}  !≤  #{foo => 1, a     => β}
  % #{foo => int(), _\foo => any()}  !≤  #{foo => 1, a\foo => β}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(tvar(alpha), tvar(beta))
  ]),
  test_utils:test_tally([{L, R}], test_utils:solutions(0)).

maps_norm_opt_10_test() ->
  % #{foo => 1, bar => 2}  ≤  #{a => 1, β => γ}
  L = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(tatom(bar), tint(2))
  ]),
  R = tmap([
    tmap_field_opt(tvar(alpha), tint(1)),
    tmap_field_opt(tvar(beta), tvar(gamma))
    ]),

  test_utils:test_tally([{L, R}],test_utils:solutions(2)).

maps_norm_opt_11_test() ->
  % #{a => β, _   => any()}  ≤  #{γ => δ, _   => any()}
  % #{a => β, _\a => any()}  ≤  #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(tvar(alpha), tvar(beta)),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(tvar(gamma), tvar(delta)),
    tmap_field_opt(tany(), tany())
  ]),
  test_utils:test_tally([{L, R}], test_utils:solutions(4)).

maps_norm_opt_12_test() ->
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ              => δ}
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ\int()\atom() => δ}
  L = tmap([
    tmap_field_opt(tint(), tatom()),
    tmap_field_opt(tatom(), tint())
  ]),
  R = tmap([
    tmap_field_opt(tint(), tvar(alpha)),
    tmap_field_opt(tatom(), tvar(beta)),
    tmap_field_opt(tvar(gamma), tvar(delta))
  ]),
  test_utils:test_tally([{L, R}], test_utils:solutions(1)).

maps_norm_opt_13_test() ->
  % #{foo => int(), _     => atom()}  ≤  #{a => β, _   => any()} | #{γ => δ, _   => any()}
  % #{foo => int(), _\foo => atom()}  ≤  #{a => β, _\a => any()} | #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = tunion(
    tmap([
      tmap_field_opt(tvar(alpha), tvar(beta)),
      tmap_field_opt(tany(), tany())
    ]),
    tmap([
      tmap_field_opt(tvar(gamma), tvar(delta)),
      tmap_field_opt(tany(), tany())
    ])
  ),

  test_utils:test_tally([{L, R}], test_utils:solutions(16)).

maps_norm_opt_14_test() ->
  % #{β_0 => β_1} ≤ {a => b}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_opt(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b))
  ]),
  Subst = #{beta_0 => tatom(a), beta_1 => tatom(b)},
  test_utils:test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}],
    [ {Subst, Subst} ]).

maps_norm_opt_15_test() ->
  % #{a => β_1, 20 => β_3} ≤ {a => b, 20 => 21}
  L = tmap([
    tmap_field_opt(tatom(a), tvar(beta_1)),
    tmap_field_opt(tint(20), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b)),
    tmap_field_opt(tint(20), tint(21))
  ]),
  test_utils:test_tally([{L, R}], [ {#{beta_1 => tnone(), beta_3 => tnone()}, #{beta_1 => tatom(b), beta_3 => tint(21)}} ]).

maps_norm_req_1_test() ->
  % #{β_0 := β_1} ≤ {atom() => int()}
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(), tint())
  ]),
  test_utils:test_tally([{L, R}, {tatom(a), tvar(beta_0)}, {tint(1), tvar(beta_1)}], [ 
    {
      #{beta_0 => tatom(a), beta_1 => tint(1)}, 
      #{beta_0 => tatom(), beta_1 => tint()}  % cleaned solution is exact
    }]).

maps_norm_req_2_test() ->
  % #{β_0 := β_1, β_2     := β_3} ≤ {a := b, 20   := 21}
  % #{β_0 := β_1, β_2\β_0 := β_3} ≤ {a := b, 20\a := 21}
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1)),
    tmap_field_req(tvar(beta_2), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_utils:test_tally([{L, R}], test_utils:solutions(10)).


maps_norm_req_3_test() ->
  % #{β_0 := β_1, β_2 := β_3} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1, 20 ≤ β_2, 21 ≤ β_3
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1)),
    tmap_field_req(tvar(beta_2), tvar(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_utils:test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}, {tint(20), tvar(beta_2)}, {tint(21), tvar(beta_3)}],
    [{
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tint(20), beta_3 => tint(21)}, 
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tany(), beta_3 => tint(21)} % cleaned solution is exact
    }]
  ).

maps_norm_req_4_test() ->
  % #{β_0 := β_1} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_req(tvar(beta_0), tvar(beta_1))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_utils:test_tally(
    [{L, R}, {tatom(a), tvar(beta_0)}, {tatom(b), tvar(beta_1)}],
    test_utils:solutions(0)
  ).

% #201
% debug tallying ([] ['k 'v] [ ( (('k, 'v), Empty -> Any) , (('a0, 'a1), Empty -> Any) ) ('k, 'a0) ((`ok, 'a1) | `error, (`ok, 'v) | `error) ]);;
% Result:  [{'a1:='v | 'a1a1; 'a0:='k | 'a0a0}]
% Cleaned: [{'a1:='v        ; 'a0:='k}]
maps_issue_201_test() ->
  {K, V} = {tvar(k), tvar(v)},
  L = tmap([ tmap_field_opt(K, V) ]),
  R = tmap([ tmap_field_opt(tvar(alpha_0), tvar(alpha_1)) ]),
  test_utils:test_tally(
    [
      % {scsubty, 14:21, {ok, $1} | error, {ok, V} | error},
      {tunion([ttuple([tatom(ok), tvar('alpha_1')]), tatom(error)]), tunion([ttuple([tatom(ok), V]), tatom(error)])}, 
      % {scsubty, 14:31, K, $0},
      {K, tvar(alpha_0)}, 
      % {scsubty, 14:36, #{K => V}, #{$0 => $1}}]
      {L, R}
    ],
    test_utils:solutions(1),
    % Fixed: K, V
    [k, v]
  ).