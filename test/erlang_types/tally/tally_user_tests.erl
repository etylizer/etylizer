-module(tally_user_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun2/3, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_req/2,
                   tyscm/2
                  ]).
-import(test_utils, [named/2]).
                


% #201
% type M('k, 'v) =  (('k, 'v), Empty -> Any);;
% debug tallying ([] ['k 'v] [ ( M('k, 'v) , (('a0, 'a1), Empty -> Any) ) ('k, 'a0) ((`ok, 'a1) | `error, (`ok, 'v) | `error) ]);;
% Result:  [{'a1:='v | 'a1a1; 'a0:='k | 'a0a0}]
% Cleaned: [{'a1:='v        ; 'a0:='k}]
maps_issue_201_test() ->
  {K, V} = {tvar(k), tvar(v)},
  L = tmap([ tmap_field_opt(K, V) ]),
  R = tmap([ tmap_field_opt(tvar(alpha_0), tvar(alpha_1)) ]),

  Sym = test_utils:extend_symtab(t, tyscm([k, v], L)),
  
  test_utils:test_tally(
    [
      % {scsubty, 14:21, {ok, $1} | error, {ok, V} | error},
      {tunion([ttuple([tatom(ok), tvar('alpha_1')]), tatom(error)]), tunion([ttuple([tatom(ok), V]), tatom(error)])}, 
      % {scsubty, 14:31, K, $0},
      {K, tvar(alpha_0)}, 
      % {scsubty, 14:36, t(K, V), #{$0 => $1}}]
      {named(t, [K, V]), R}
    ],
    test_utils:solutions(1),
    % Fixed: K, V
    [k, v],
    Sym
  ).
