-module(constraints_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

constrs_test_() ->
  {timeout, 15, fun() ->
    global_state:with_new_state(fun() ->
      % load all nodes directly, assume no collisions
      {ok, [TallyConstraints, GlobalSystem]} = file:consult("test_files/erlang_types/constraints/sets-union2.config"),

      lists:foreach(fun(Types) -> maps:foreach(fun(Node, Descriptor) -> 
        ty_node:force_load(Node, Descriptor)
      end, Types) end, GlobalSystem),

      MonomorphicVariables = #{{var,name,'Element'} => []},
      true = etally:is_tally_satisfiable(TallyConstraints, MonomorphicVariables),
      ok
    end)
                end
  }.
