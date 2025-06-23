-module(subtype_user_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

simple_named_test() ->
  S = tnamed(mynamed, [int()]),
  T = tnamed(mynamed, [b(ok)]),

  with_symtab(fun() ->
    true = is_subtype_stateful(S, S) and is_subtype_stateful(T, T),
    false = is_subtype_stateful(S, T),
    false = is_subtype_stateful(T, S)

    end,
    [{test_key(mynamed, 1), tyscm([a], f([v(a), v(a)], b(ok)))}]
  ).

simple_recursive_test() ->
  S = tnamed(ty, []),
  with_symtab(fun() ->
    true = is_subtype_stateful(S, S)
    end,
    [ {test_key(ty), tyscm([], ttuple([ b(tuple), tlist(S)])) } ]
  ).

% #182
mu_test() ->
  S = tmu(tvar_mu(exp), ttuple([u([b(a), tvar_mu(exp)])])),
  true = is_subtype(S, S).

% #182
exp_test() ->
  S = tnamed(exp),
  with_symtab(fun() ->
    true = is_subtype_stateful(S, S)
    end,
    [ {test_key(exp), tyscm([], ttuple([u([b(a), S])])) } ]
  ).

funs_test() ->
  S = tnamed(exp),
  with_symtab(fun() ->
    true = is_subtype_stateful(S, S)
    end,
    [ {test_key(exp), tyscm([], f([u([b(a), S])], b(b))) } ]
  ).

% TODO rewrite 
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

%%
%%
%%
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
