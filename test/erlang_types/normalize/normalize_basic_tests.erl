-module(normalize_basic_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

basic_test() ->
  with_symtab(
    fun() -> 
      T1 = ty_parser:parse(tnamed(plus)),
      T2 = ty_parser:parse(tnamed(vars)),

      SnT1 = ty_node:difference(T1, T2),
      Norm = ty_node:normalize(SnT1, #{}),

      % solutions: variable 1 or 2 empty or int constraints on both variables
      3 = length(Norm),

      SnT2 = ty_parser:parse(tnamed(c1)),
      Norm2 = ty_node:normalize(SnT2, #{}),
      % single constraint
      1 = length(Norm2),

      % 1 constraint can be filtered (one variable cannot be empty anymore)
      Meet = constraint_set:meet(Norm, Norm2, #{}),
      2 = length(Meet),

      ok
    end, system("test_files/erlang_types/normalize/plus.config")).

mk_diff_test() ->
  with_type(
    fun(Type) -> 
      [] = ty:normalize(Type, #{}),
      ok
    end, system("test_files/erlang_types/normalize/mk_diff_bad.config")).

queue_slow1_test() ->
  with_type(
    fun(Type) -> 
      FixedVariables = #{{var,name,'Item'} => [],{var,name,'Q1'} => [],{var,name,'Q2'} => []},
      V = ty:normalize(Type, FixedVariables),
      4 = length(V) % was 19 before minimization
    end, system("test_files/erlang_types/normalize/queue19.config")),

  with_type(
    fun(Type) -> 
      FixedVariables = #{{var,name,'Item'} => [],{var,name,'Q1'} => [],{var,name,'Q2'} => []},
      V = ty:normalize(Type, FixedVariables),
      4 = length(V) % was 10 before 
    end, system("test_files/erlang_types/normalize/queue10.config")).

