-module(substitution_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

variable_test() ->
  global_state:with_new_state(fun() ->

    % T1 = mu X.  [] | (alpha<1> , X)
    % T2 = mu Y.  [] | (alpha<1>, Y)
    % 
    % T1 = mu X.  [] | (integer<ID::2> , X)
    % T2 = mu Y.  [] | (integer<ID::2>, Y)
    % 
    % substitution: alpha -> integer() :: O
    
    % O(T1) = ID1
    % O(T2) = ID2
    % 
    % ID1 = ID2

    Ty = ty_parser:parse({var, alpha}),
    Tyy = ty_node:dump(Ty),
    #{{node, 1} := {node, _, {leaf, Any}, {leaf, Empty}}} = Tyy,
    gt = ty_rec:compare(Any, Empty),
    ok



  end).