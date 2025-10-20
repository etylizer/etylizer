-module(tally_map_tests).

-compile([nowarn_unused_function]). % ignore unused helper functions

-import(erlang_types_test_utils, [test_tally/3, test_tally/2, solutions/1]).

-include_lib("eunit/include/eunit.hrl").

% AST helper functions
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").


% =====
% Map Normalization
% =====
maps_norm_opt_1_test() ->
  % #{int() => int()} ⊏ #{a => β}
  L = tmap([tmap_field_opt(tint(), tint())]),
  R = tmap([tmap_field_opt(v(alpha), v(beta))]),

  test_tally([{L, R}],
    [{#{alpha => tint(), beta => tint()},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_2_test() ->
  % #{int() => int(), atom() => atom()}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tatom(), tatom())
  ]),
  R = tmap([tmap_field_opt(v(alpha), v(beta))]),

  test_tally([{L, R}],
    [{#{alpha => u(tint(), tatom()), beta => u(tint(), tatom())},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_3_test() ->
  % #{int() => int(), _       => foo}  ≤  #{a => β}
  % #{int() => int(), _\int() => foo}  ≤  #{a => β}
  L = tmap([
    tmap_field_opt(tint(), tint()),
    tmap_field_opt(tany(), tatom(foo))
  ]),
  R = tmap([tmap_field_opt(v(alpha), v(beta))]),

  test_tally([{L, R}],
    [{#{alpha => tany(), beta => u(tint(), tatom(foo))},
      #{alpha => tany(), beta => tany()}}
    ]).

maps_norm_opt_4_test() ->
  % #{a => int()}  ≤  #{int() => β}
  L1 = tmap([tmap_field_opt(v(alpha), tint())]),
  R1 = tmap([tmap_field_opt(tint(), v(beta))]),
  test_tally([{L1, R1}], solutions(2)),

  % #{int() => β}  ≤  #{a => int()}
  L2 = tmap([tmap_field_opt(tint(), v(beta))]),
  R2 = tmap([tmap_field_opt(v(alpha), tint())]),

  test_tally([{L2, R2}], solutions(2)).

maps_norm_opt_5_test() ->
  % #{a => int(), _   => atom()}  ≤  #{β => atom() | int()}
  % #{a => int(), _\a => atom()}  ≤  #{β => atom() | int()}
  L = tmap([
    tmap_field_opt(v(alpha), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = tmap([
    tmap_field_opt(v(beta), u(tatom(), tint()))
  ]),

  test_tally([{L, R}], solutions(3)).

maps_norm_opt_6_test() ->
  % #{a => β} ≤ #{atom() => int()}
  L = tmap([tmap_field_opt(v(alpha), v(beta))]),
  R = tmap([tmap_field_opt(tatom(), tint())]),

  test_tally([{L, R}], solutions(3)).


maps_norm_opt_7_test() ->
  % #{a => atom()}  ≤  #{β => any()}
  L = tmap([
    tmap_field_opt(v(alpha), tatom())
  ]),
  R = tmap([
    tmap_field_opt(v(beta), tany())
  ]),
  test_tally([{L, R}], solutions(2)).

maps_norm_opt_8_test() ->
  % #{}  ≤  #{a => β}
  L = tmap([]),
  R1 = tmap([tmap_field_opt(v(alpha), v(beta))]),
  test_tally([{L, R1}], solutions(1)),

  % #{}  ≤  #{a => β} /\ #{}
  R2 = i([R1, L]),
  test_tally([{L, R2}], solutions(1)).

maps_norm_opt_9_test() ->
  % #{foo => int(), _     => any()}  !≤  #{foo => 1, a     => β}
  % #{foo => int(), _\foo => any()}  !≤  #{foo => 1, a\foo => β}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(v(alpha), v(beta))
  ]),
  test_tally([{L, R}], solutions(0)).

maps_norm_opt_10_test() ->
  % #{foo => 1, bar => 2}  ≤  #{a => 1, β => γ}
  L = tmap([
    tmap_field_opt(tatom(foo), tint(1)),
    tmap_field_opt(tatom(bar), tint(2))
  ]),
  R = tmap([
    tmap_field_opt(v(alpha), tint(1)),
    tmap_field_opt(v(beta), v(gamma))
    ]),

  test_tally([{L, R}],solutions(2)).

maps_norm_opt_11_test() ->
  % #{a => β, _   => any()}  ≤  #{γ => δ, _   => any()}
  % #{a => β, _\a => any()}  ≤  #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(v(alpha), v(beta)),
    tmap_field_opt(tany(), tany())
  ]),
  R = tmap([
    tmap_field_opt(v(gamma), v(delta)),
    tmap_field_opt(tany(), tany())
  ]),
  test_tally([{L, R}], solutions(8)).

maps_norm_opt_12_test() ->
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ              => δ}
  % #{int() => atom(), atom() => int()}  ≤  #{int() => a, atom() => β, γ\int()\atom() => δ}
  L = tmap([
    tmap_field_opt(tint(), tatom()),
    tmap_field_opt(tatom(), tint())
  ]),
  R = tmap([
    tmap_field_opt(tint(), v(alpha)),
    tmap_field_opt(tatom(), v(beta)),
    tmap_field_opt(v(gamma), v(delta))
  ]),
  test_tally([{L, R}], solutions(1)).

maps_norm_opt_13_test() ->
  % #{foo => int(), _     => atom()}  ≤  #{a => β, _   => any()} | #{γ => δ, _   => any()}
  % #{foo => int(), _\foo => atom()}  ≤  #{a => β, _\a => any()} | #{γ => δ, _\γ => any()}
  L = tmap([
    tmap_field_opt(tatom(foo), tint()),
    tmap_field_opt(tany(), tatom())
  ]),
  R = u(
    tmap([
      tmap_field_opt(v(alpha), v(beta)),
      tmap_field_opt(tany(), tany())
    ]),
    tmap([
      tmap_field_opt(v(gamma), v(delta)),
      tmap_field_opt(tany(), tany())
    ])
  ),

  test_tally([{L, R}], solutions(16)).

maps_norm_opt_14_test() ->
  % #{β_0 => β_1} ≤ {a => b}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_opt(v(beta_0), v(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b))
  ]),
  Subst = #{beta_0 => tatom(a), beta_1 => tatom(b)},
  test_tally(
    [{L, R}, {tatom(a), v(beta_0)}, {tatom(b), v(beta_1)}],
    [ {Subst, Subst} ]).

maps_norm_opt_15_test() ->
  % #{a => β_1, 20 => β_3} ≤ {a => b, 20 => 21}
  L = tmap([
    tmap_field_opt(tatom(a), v(beta_1)),
    tmap_field_opt(tint(20), v(beta_3))
  ]),
  R = tmap([
    tmap_field_opt(tatom(a), tatom(b)),
    tmap_field_opt(tint(20), tint(21))
  ]),
  test_tally([{L, R}], [ {#{beta_1 => tnone(), beta_3 => tnone()}, #{beta_1 => tatom(b), beta_3 => tint(21)}} ]).

maps_norm_req_1_test() ->
  % #{β_0 := β_1} ≤ {atom() => int()}
  L = tmap([
    tmap_field_req(v(beta_0), v(beta_1))
  ]),
  R = tmap([
    tmap_field_opt(tatom(), tint())
  ]),
  test_tally([{L, R}, {tatom(a), v(beta_0)}, {tint(1), v(beta_1)}], [ 
    {
      #{beta_0 => tatom(a), beta_1 => tint(1)}, 
      #{beta_0 => tatom(), beta_1 => tint()}  % cleaned solution is exact
    }]).

maps_norm_req_2_test() ->
  % #{β_0 := β_1, β_2     := β_3} ≤ {a := b, 20   := 21}
  % #{β_0 := β_1, β_2\β_0 := β_3} ≤ {a := b, 20\a := 21}
  L = tmap([
    tmap_field_req(v(beta_0), v(beta_1)),
    tmap_field_req(v(beta_2), v(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally([{L, R}], solutions(9)).


maps_norm_req_3_test() ->
  % #{β_0 := β_1, β_2 := β_3} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1, 20 ≤ β_2, 21 ≤ β_3
  L = tmap([
    tmap_field_req(v(beta_0), v(beta_1)),
    tmap_field_req(v(beta_2), v(beta_3))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally(
    [{L, R}, {tatom(a), v(beta_0)}, {tatom(b), v(beta_1)}, {tint(20), v(beta_2)}, {tint(21), v(beta_3)}],
    [{
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tint(20), beta_3 => tint(21)}, 
      #{beta_0 => tatom(a), beta_1 => tatom(b), beta_2 => tany(), beta_3 => tint(21)} % cleaned solution is exact
    }]
  ).

maps_norm_req_4_test() ->
  % #{β_0 := β_1} ≤ {a := b, 20 := 21}, a ≤ β_0, b ≤ β_1
  L = tmap([
    tmap_field_req(v(beta_0), v(beta_1))
  ]),
  R = tmap([
    tmap_field_req(tatom(a), tatom(b)),
    tmap_field_req(tint(20), tint(21))
  ]),
  test_tally(
    [{L, R}, {tatom(a), v(beta_0)}, {tatom(b), v(beta_1)}],
    solutions(0)
  ).

% #201
% debug tallying ([] ['k 'v] [ ( (('k, 'v), Empty -> Any) , (('a0, 'a1), Empty -> Any) ) ('k, 'a0) ((`ok, 'a1) | `error, (`ok, 'v) | `error) ]);;
% Result:  [{'a1:='v | 'a1a1; 'a0:='k | 'a0a0}]
% Cleaned: [{'a1:='v        ; 'a0:='k}]
maps_issue_201_test() ->
  {K, V} = {v(k), v(v)},
  L = tmap([ tmap_field_opt(K, V) ]),
  R = tmap([ tmap_field_opt(v(alpha_0), v(alpha_1)) ]),
  test_tally(
    [
      % {scsubty, 14:21, {ok, $1} | error, {ok, V} | error},
      {u([ttuple([tatom(ok), v('alpha_1')]), tatom(error)]), u([ttuple([tatom(ok), V]), tatom(error)])}, 
      % {scsubty, 14:31, K, $0},
      {K, v(alpha_0)}, 
      % {scsubty, 14:36, #{K => V}, #{$0 => $1}}]
      {L, R}
    ],
    solutions(1),
    % Fixed: K, V
    [k, v]
  ).
