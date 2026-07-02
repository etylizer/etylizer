-module(subtype_user_tests).
-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

simple_named_test() ->
  S = tnamed(mynamed, [tint()]),
  T = tnamed(mynamed, [b(ok)]),

  with_symtab(fun() ->
    true = is_subtype_stateful(S, S) and is_subtype_stateful(T, T),
    false = is_subtype_stateful(S, T),
    false = is_subtype_stateful(T, S)

    end,
    [{test_key(mynamed, 1), tyscm([a], f([v(a), v(a)], b(ok)))}]
  ).

simple_named2_test() ->
  S = tnamed(mynamed, [b(helloworld)]),
  T = b(helloworld),
  with_symtab(
    fun() -> 
      true = is_subtype_stateful(S, T),
      true = is_subtype_stateful(T, S)
    end, 
    [ 
     {test_key(mynamed2, 1), tyscm([a], b(helloworld))}, 
     {test_key(mynamed, 1), tyscm([a], tnamed(mynamed2, [v(a)]))} 
    ]).

simple_recursive_test() ->
  S = tnamed(ty, []),
  with_symtab(fun() ->
    true = is_subtype_stateful(S, S)
    end,
    [ {test_key(ty), tyscm([], ttuple([ b(tuple), tlist(S)])) } ]
  ).

simple_recursive2_test() ->
  with_symtab(
    fun() -> 
        S = tnamed(mylist, [b(myints)]), 
        T = b(helloworld), 
        false = is_subtype_stateful(S, T)
    end,
    [{test_key(mylist, 1), tyscm([a], u([b(emptylist), ttuple([v(a), tnamed(mylist, [v(a)])])]))}]
  ).

funs_test() ->
  S = tnamed(exp),
  with_symtab(fun() ->
    true = is_subtype_stateful(S, S)
    end,
    [ {test_key(exp), tyscm([], f([u([b(a), S])], b(b))) } ]
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

simple_basic_ulist_test() ->
  with_symtab(
    fun() ->
      S = tnamed(ulist, [tint()]),
      T = tnamed(ulist, [b(float)]),
      true = is_subtype_stateful(S, S),
      false = is_subtype_stateful(S, T),
      false = is_subtype_stateful(T, S)
    end,
    system("test_files/erlang_types/subtype/system_lists")
  ).

% µx.(α×(α×x)) ∨ nil  ≤ µx.(α×x)     ∨ nil
% µx.(α×x)     ∨ nil !≤ µx.(α×(α×x)) ∨ nil
even_lists_contained_in_lists_test() ->
  with_symtab(
    fun() ->
      S = tnamed(even_ulist, [v(alpha)]),
      T = tnamed(ulist, [v(alpha)]),
      true = is_subtype_stateful(S, T),
      false = is_subtype_stateful(T, S)
    end,
    system("test_files/erlang_types/subtype/system_lists")
  ).

% µx.(α×(α×x)) ∨ (α×nil)  ≤ µx.(α×x)     ∨ nil
% µx.(α×x)     ∨ (α×nil) !≤ µx.(α×(α×x)) ∨ nil
uneven_lists_contained_in_lists_test() ->
  with_symtab(
    fun() ->
      S = tnamed(uneven_ulist, [v(alpha)]),
      T = tnamed(ulist, [v(alpha)]),
      true = is_subtype_stateful(S, T),
      false = is_subtype_stateful(T, S)
    end,
    system("test_files/erlang_types/subtype/system_lists")
  ).

% µx.(α×x) ∨ nil ∼ (µx.(α×(α×x))∨nil) ∨ (µx.(α×(α×x))∨(α×nil))
uneven_even_lists_contained_in_lists_test() ->
  with_symtab(
    fun() -> 
      S = u([tnamed(uneven_ulist, [v(alpha)]), tnamed(even_ulist, [v(alpha)])]), 
      T = tnamed(ulist, [v(alpha)]),
      true = is_subtype_stateful(S, T),
      true = is_subtype_stateful(T, S)
    end,
    system("test_files/erlang_types/subtype/system_lists")
  ).

% (µx.(α×(α×x))∨nil) <!> (µx.(α×(α×x))∨(α×nil))
uneven_even_lists_not_comparable_test() -> 
  with_symtab(
    fun() -> 
      S = tnamed(uneven_ulist, [v(alpha)]),
      T = tnamed(even_ulist, [v(alpha)]),
      false = is_subtype_stateful(S, T),
      false = is_subtype_stateful(T, S)
    end,
    system("test_files/erlang_types/subtype/system_lists")
  ).
