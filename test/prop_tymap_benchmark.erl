-module(prop_tymap_benchmark).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-define(X, begin tvar('X') end).
-define(Y, begin tvar('Y') end).
-define(K, begin tvar('K') end).
-define(K1, begin tvar('K1') end).
-define(K2, begin tvar('K2') end).
-define(V, begin tvar('V') end).
-define(V1, begin tvar('V1') end).
-define(V2, begin tvar('V2') end).
-define(V3, begin tvar('V3') end).
-define(A, begin tvar('A') end).
-define(A1, begin tvar('A1') end).
-define(A2, begin tvar('A2') end).
-define(B, begin tvar('B') end).
-define(B1, begin tvar('B1') end).
-define(B2, begin tvar('B2') end).
-define(B3, begin tvar('B3') end).
-define(Def, begin tvar('Def') end).
-define(Init, begin tvar('Init') end).
-define(F(Z), fun() -> Z end).

-define(ETY, fun(T) -> ast_lib:ast_to_erlang_ty(T) end).
-define(FUN1, fun(Dom, Codom) -> mk_fun(mk_h(Dom, Codom)) end).
-define(FUN2, fun(Dom1, Codom1, Dom2, Codom2) -> mk_fun(mk_h(Dom1, Codom1) ++ mk_h(Dom2, Codom2)) end).


-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2,
                   tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
                   tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0,
                   tfloat/0, tfun/2, tfun_any/0, tnot/1, tbool/0,
                   tmap/1, tmap_any/0, tmap_field_opt/2, tmap_field_man/2
                  ]).


-type f() :: {ActualFun::ety(), Domain::ety(), f_helper()}.
-type ety() :: {ty_ref, integer()}.

-type f_helper() :: list(list({[ast:ty()], ast:ty()})).
-type subty() :: {ety(), ety()}.

-type condition_union() :: {union, [condition_intersect()]}.
-type condition_intersect() :: {intersect, [condition()]}.
-type condition() :: {If::subty(), ThenReturn:: ety()}.


-spec mk_fun(f_helper()) -> f().
mk_fun(Fs) ->
  AstFun = tunion([tintersect([tfun(Dom, Codom) || {Dom, Codom} <- IntFs]) || IntFs <- Fs]),
  EtyFun = ?ETY(AstFun),
  {EtyFun, domain(Fs), Fs}.

-spec mk_h([ast:ty()], ast:ty()) -> f_helper().
mk_h(Dom, Codom) -> [[{Dom, Codom}]].

-spec mk_condition(ety(), ety(), fun(() -> ety())) -> condition().
mk_condition(S, T, R) -> {{S, T}, R}.

-spec domain(f_helper()) -> ety().
domain([]) -> ?ETY(tany());
domain([[] | _]) -> ?ETY(tnone());
domain([IntFs | UnionFs]) ->
  ?ETY(tintersect([
    domain(UnionFs),
    tunion([ttuple(Dom) || {Dom, _} <- IntFs])
  ])).

-spec apply_to(f_helper(), ety(), _) -> condition_union().
apply_to(Fs, Args, Substitution) ->
    IntCond =
      fun(Fs) ->
        {intersect, [mk_condition(
          ty_rec:substitute(Args, Substitution),
          ty_rec:substitute(?ETY(ttuple(Dom)), Substitution),
          ?F(ty_rec:substitute(?ETY(Codom), Substitution))
        ) || {Dom, Codom} <- Fs]
        }
      end,
    {union, [IntCond(IntFs) || IntFs <- Fs]}.


-spec eval_union(condition_union()) -> ety().
eval_union({union, IntCond}) ->
  lists:foldr(fun ty_rec:union/2, ?ETY(tnone()), [eval_intcond(C) || C <- IntCond]).

eval_intcond({intersect, C}) ->
  case eval_cond(C) of
    [] -> ?ETY(tnone());
    Etys -> lists:foldr(fun ty_rec:intersect/2, ?ETY(tany()), Etys)
  end.

eval_cond(C) ->
  Result = fun({error, _}) -> false; (_) -> true end,
  [Ety3() || {{Ety1, Ety2}, Ety3} <- C, Result(etally:tally([{Ety1, Ety2}]))].


-spec application(f(), Args::ety()) -> {ok, Result::ety()} | error.
application({EtyFun, EtyDom, Fs}, Args) ->
  ConstrFun = {EtyFun, ?ETY(tfun_any())},
  ConstrDom = {Args, EtyDom},
  Subst = etally:tally([ConstrFun, ConstrDom]),

  case Subst of
    {error, _} -> error;
    _ ->
      EtyResult = eval_union(apply_to(Fs, Args, Subst)),
      case EtyResult == ?ETY(tnone()) of
        true -> error;
        false -> EtyResult
      end
  end.



%%%%%%%%%%%%%%%%%%%%%%%%
%%%    Generators    %%%
%%%%%%%%%%%%%%%%%%%%%%%%

map_empty() -> a.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%    Meta Properties    %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prop_get2_if_present() -> ok.

prop_get3_if_present() -> ok.

prop_find_if_present() -> ok.

prop_is_key_if_present() -> ok.

prop_take_if_present() -> ok.

prop_update_if_present() -> ok.

prop_update_with3_if_present() -> ok.

prop_update_with4_happens() -> ok.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%      Maps Library Functions      %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get2() ->
  ?FUN1([?K, tmap([tmap_field_man(?K, ?V), tmap_field_opt(tany(), tany())])], ?V).

get3() ->
  TyMap1 = tmap([tmap_field_man(?K, ?V), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_opt(?K, ?V)]),
  ?FUN2(
    [?K, TyMap1, tany()],
    ?V,

    [tany(), TyMap2, ?Def],
    tunion(?V, ?Def)
  ).

find() ->
  ?FUN2(
    [?K, tmap([tmap_field_man(?K, ?V), tmap_field_opt(tany(), tany())])],
    ttuple([tatom(ok), ?V]),

    [tany(), tmap([tmap_field_opt(?K, ?V)])],
    tunion(ttuple([tatom(ok), ?V]), tatom(error))
  ).

from_list() ->
  ?FUN1([tlist(ttuple([?K, ?V]))], tmap([tmap_field_opt(?K, ?V)])).

from_keys() ->
  ?FUN1([tlist(?K), ?V], tmap([tmap_field_opt(?K, ?V)])).

intersect() ->
  BoundedK = tintersect([?K, ?K1, ?K2]),
  ?FUN1(
    [tmap([tmap_field_opt(?K1, tany())]), tmap([tmap_field_opt(?K2, ?V)])],
    tmap([tmap_field_opt(BoundedK, ?V)])
  ).

intersect_with() ->
  BoundedK = tintersect([?K, ?K1, ?K2]),
  ?FUN1(
    [
      tfun([?K, ?V1, ?V2], ?V),
      tmap([tmap_field_opt(?K1, ?V1)]),
      tmap([tmap_field_opt(?K2, ?V2)])
    ],
    tmap([tmap_field_opt(BoundedK, ?V)])
  ).

is_key() ->
  ?FUN2(
    [?K, tmap([tmap_field_man(?K, tany()), tmap_field_opt(tany(), tany())])],
    tatom(true),

    [tany(), tmap_any()],
    tbool()
  ).

keys() ->
  ?FUN1(
    [tmap([tmap_field_man(?K, tany()), tmap_field_opt(?A, tany())])],
    tlist(tunion(?K, ?A))
  ).

merge() ->
  ?FUN1(
    [
      tmap([tmap_field_opt(?K1, ?V1), tmap_field_opt(?A1, ?B1)]),
      tmap([tmap_field_opt(?K2, ?V2), tmap_field_opt(?A2, ?B2)])
    ],
    tmap([
      tmap_field_man(tunion(?K1, ?K2), tunion(?V1, ?V2)),
      tmap_field_opt(tunion(?A1, ?A2), tunion(?B1, ?B2))])
  ).

merge_with() ->
  ?FUN1(
    [
      tfun([tunion(?K1, ?K2), ?V1, ?V2], ?V3),
      tmap([tmap_field_opt(?K1, ?V1)]),
      tmap([tmap_field_opt(?K2, ?V2)])
    ],
    tmap([tmap_field_opt(tunion(?K1, ?K2), tunion([?V1, ?V2, ?V3]))])
  ).

put() ->
  %% -spec put(K, V, #{X := Y, A => B}) -> #{X := Y|V, A => B|V}.
  TyMap1 = tmap([tmap_field_man(?X, ?Y), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_man(?X, tunion(?Y, ?V)), tmap_field_opt(tunion(?A, ?K), tunion(?B, ?V))]),
  ?FUN1(
    [?K, ?V, TyMap1],
    TyMap2
  ).

remove() ->
  TyMap = tmap([tmap_field_opt(?A, ?B)]),
  ?FUN1([?K, TyMap], TyMap).

take() ->
  %% TODO think
  TyMap1 = tmap([tmap_field_man(?K, ?V), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_opt(?A, ?B)]),
  ?FUN2(
    [?K, TyMap1],
    ttuple([?V, TyMap1]),

    [?K, TyMap2],
    tunion(ttuple([?B, TyMap2]), tatom(error))
  ).

to_list() ->
  ?FUN1([tmap([tmap_field_opt(?K, ?V)])], tlist(ttuple([?K, ?V]))).

update() ->
  TyMap1 = tmap([tmap_field_man(?K, ?Y), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_man(?K, tunion(?Y, ?V)), tmap_field_opt(?A, ?B)]),
  ?FUN1([?K, ?V, TyMap1], TyMap2).

values() ->
  ?FUN1(tmap([tmap_field_opt(tany(), ?V)]), tlist(?V)).

update_with3() ->
  TyMap1 = tmap([tmap_field_man(?K, ?V1), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_man(?K, tunion(?V1, ?V2)), tmap_field_opt(?A, ?B)]),
  ?FUN1([tfun([?V1], ?V2), TyMap1], TyMap2).

update_with4() ->
  TyMap1 = tmap([tmap_field_man(?X, ?V), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_man(?X, tunion(?V, ?Y)), tmap_field_opt(tunion(?A, ?K), tunion([?B, ?Y, ?Init]))]),
  ?FUN1([tfun([?V], ?Y), TyMap1], TyMap2).

filter() ->
  ?FUN1(
    [
      tfun([tunion(?K, ?A), tunion(?V, ?B)], tbool()),
      tmap([tmap_field_man(?K, ?V), tmap_field_opt(?A, ?B)])
    ],
    tmap([tmap_field_opt(?K, ?V), tmap_field_opt(?A, ?B)])
  ).

filtermap() ->
  ?FUN1(
    [
      tfun(
        [tunion(?K, ?A), tunion(?V1, ?B)],
        tunion(tbool(), ttuple([tatom(true), ?V2]))
      ),
      tmap([tmap_field_man(?K, ?V1), tmap_field_opt(?A, ?B)])
    ],
    tmap([tmap_field_opt(?K, tunion(?V1, ?V2)), tmap_field_opt(?A, tunion(?B, ?V2))])
  ).

map() ->
  ?FUN1(
    [
      tfun([?K, ?V1], ?V2),
      tmap([tmap_field_opt(?K,  ?V1)])
    ],
    tmap([tmap_field_opt(?K, ?V2)])
  ).

with() ->
  ?FUN1(
    [tlist(?K), tmap([tmap_field_opt(tunion(?K, ?A), ?V)])],
    tmap([tmap_field_opt(?K, ?V)])
  ).

without() ->
  TyMap = tmap([tmap_field_opt(?A, ?B)]),
  ?FUN1([tlist(?K), TyMap], TyMap).


alternative_merge_with() ->
  TyFun = tintersect([
    tfun([tunion(?K1, ?K2), ?V1, ?V2], ?V3),
    tfun([tunion(?A1, ?A2), ?B1, ?B2], ?B3)
  ]),
  ?FUN1(
    [
      TyFun,
      tmap([tmap_field_man(?K1, ?V1), tmap_field_opt(?A1, ?B1)]),
      tmap([tmap_field_man(?K2, ?V2), tmap_field_opt(?A2, ?B2)])
    ],
    tmap([
      tmap_field_man(tunion(?K1, ?K2), ?V3),
      tmap_field_opt(tunion(?A1, ?A2), tunion([?B1, ?B2, ?B3]))
    ])
  ).

alternative_put() ->
  ?FUN1(
    [?K, ?V, tmap([tmap_field_opt(?A, ?B)])],
    tmap([tmap_field_opt(?K, ?V), tmap_field_opt(?A, ?B)])
  ).

alternative_take() ->
  TyMap1 = tmap([tmap_field_opt(?K, ?V), tmap_field_opt(?A, ?B)]),
  TyMap2 = tmap([tmap_field_opt(?A, ?B)]),
  ?FUN1([?K, TyMap1], TyMap2).

alternative_map() ->
  TyFun = tintersect([
    tfun([?K, ?V1], ?V2),
    tfun([?A, ?B1], ?B2)
  ]),
  ?FUN1(
    [TyFun, tmap([tmap_field_opt(?K, ?V1), tmap_field_opt(?A, ?B1)])],
    tmap([tmap_field_opt(?K, ?V2), tmap_field_opt(?A, ?B2)])
  ).
