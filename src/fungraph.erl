-module(fungraph).

-include("log.hrl").

-ifdef(TEST).
-export([dependency_order/1]).
-endif.

-type call_vertex() :: {Name::atom(), Arity::arity()}.
-type call_graph() :: graph:graph(call_vertex()).

-type scc() :: sets:set(call_vertex()).
-type scc_dep_graph() :: graph:graph(scc()).

-spec cv_to_string(call_vertex()) -> string().
cv_to_string({Name, Arity}) ->
    utils:sformat("~w/~w", Name, Arity).

-spec scc_to_string(scc()) -> string().
scc_to_string(SCC) ->
    L = lists:map(fun cv_to_string/1, sets:to_list(SCC)),
    string:join(L, "+").

-spec add_call_vertices(ast:forms(), call_graph()) -> #{ call_vertex() => ast:fun_decl() }.
add_call_vertices(Forms, Graph) ->
    KVs = lists:filtermap(
      fun(F) ->
          case F of
              {function, _Loc, Name, Arity, _Clauses} ->
                  K = {Name, Arity},
                  graph:add_vertex(Graph, K),
                  {true, {K, F}};
              _ -> false
          end
      end,
      Forms),
    maps:from_list(KVs).

-spec add_call_edges(ast:form(), call_graph()) -> ok.
add_call_edges({function, _Loc, Name, Arity, Clauses}, Graph) ->
    Source = {Name, Arity},
    Deps =
        utils:everything(
          fun(X) ->
                  case X of
                      {var, _, {ref, DepName, DepArity}} -> {ok, {DepName, DepArity}};
                      {fun_ref, _, {ref, DepName, DepArity}} -> {ok, {DepName, DepArity}};
                      _ -> error
                  end
          end,
          Clauses
         ),
    lists:foreach(
      fun(Target) ->
              graph:add_edge(Graph, Source, Target)
      end,
      Deps),
    ok;
add_call_edges(_, _) -> ok.

-spec dependency_order(ast:forms()) -> [sets:set(ast:fun_decl())].
dependency_order(Forms) ->
    graph:with_graph(
      fun(CallGraph) ->
              graph:with_graph(fun(SCCDepGraph) ->
                                       dependency_order(Forms, CallGraph, SCCDepGraph)
                               end)
      end).

-spec dependency_order(ast:forms(), call_graph(), scc_dep_graph()) -> [sets:set(ast:fun_decl())].
dependency_order(Forms, CallGraph, SCCDepGraph) ->
    FunMap = add_call_vertices(Forms, CallGraph),
    ?LOG_TRACE("FunMap=~200p", FunMap),
    lists:foreach(fun (Form) -> add_call_edges(Form, CallGraph) end, Forms),
    ?LOG_DEBUG("CallGraph=~200p", graph:to_list(CallGraph, fun cv_to_string/1)),
    SCCs = graph:strong_components(CallGraph),
    % SCCMap maps each vertex to its SCC (strongly connected component)
    % SCCMap: #{ call_vertex() => scc() }
    SCCMap =
        maps:from_list(
          lists:flatmap(
            fun(SCC) ->
                    lists:map(fun(V) -> {V, SCC} end, sets:to_list(SCC))
            end,
            sets:to_list(SCCs))),
    ?LOG_DEBUG("SCCMap=~p",
               lists:map(fun({K, SCC}) ->
                                 {cv_to_string(K), scc_to_string(SCC)}
                         end, maps:to_list(SCCMap))),
    % build a dependency graph among SCCs
    lists:foreach(fun (SCC) -> graph:add_vertex(SCCDepGraph, SCC) end, sets:to_list(SCCs)),
    utils:foreach(
      sets:to_list(SCCs),
      fun(SourceSCC) ->
              utils:foreach(
                sets:to_list(SourceSCC),
                fun(Fun) ->
                        CalledFuns = graph:out_neighbours(CallGraph, Fun),
                        utils:foreach(
                          CalledFuns,
                          fun(CalledFun) ->
                                  TargetSCC = maps:get(CalledFun, SCCMap),
                                  graph:add_edge(SCCDepGraph, SourceSCC, TargetSCC)
                          end)
                end)
      end),
    ?LOG_DEBUG("SCCDepGraph=~200p",
               graph:to_list(SCCDepGraph, fun scc_to_string/1)),
    % return the topological order of the dependency graph among SCCs
    SortedSCCs =
      case graph:topsort(SCCDepGraph) of
        cyclic -> errors:bug("no topological ordering exists");
        L -> lists:reverse(L)
      end,
    utils:map_flip(
      SortedSCCs,
      fun(SCC) ->
              sets:from_list(utils:map_flip(
                               sets:to_list(SCC),
                               fun(FunKey) -> maps:get(FunKey, FunMap) end
                              ))
      end
     ).
    