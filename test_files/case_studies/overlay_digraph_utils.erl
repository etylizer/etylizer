-module(overlay_digraph_utils).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of digraph_utils.erl that have none upstream.

-type successors() :: fun((digraph:graph(), digraph:vertex(), [digraph:vertex()]) -> [digraph:vertex()]).

-spec 'digraph_utils:forest'(digraph:graph(), successors()) -> [[digraph:vertex()]].
'digraph_utils:forest'(_, _) -> error(overlay).
-spec 'digraph_utils:forest'(digraph:graph(), successors(), [digraph:vertex()]) -> [[digraph:vertex()]].
'digraph_utils:forest'(_, _, _) -> error(overlay).
-spec 'digraph_utils:forest'(digraph:graph(), successors(), [digraph:vertex()], first | not_first) -> [[digraph:vertex()]].
'digraph_utils:forest'(_, _, _, _) -> error(overlay).
-spec 'digraph_utils:pretraverse'(first | not_first, digraph:vertex(), successors(), digraph:graph(),
                                  sets:set(digraph:vertex()), [[digraph:vertex()]]) ->
          {sets:set(digraph:vertex()), [[digraph:vertex()]]}.
'digraph_utils:pretraverse'(_, _, _, _, _, _) -> error(overlay).
-spec 'digraph_utils:ptraverse'([digraph:vertex()], successors(), digraph:graph(), sets:set(digraph:vertex()),
                                [digraph:vertex()], [[digraph:vertex()]]) ->
          {sets:set(digraph:vertex()), [[digraph:vertex()]]}.
'digraph_utils:ptraverse'(_, _, _, _, _, _) -> error(overlay).
-spec 'digraph_utils:revpostorder'(digraph:graph()) -> [digraph:vertex()].
'digraph_utils:revpostorder'(_) -> error(overlay).
-spec 'digraph_utils:posttraverse'([digraph:vertex()], digraph:graph(), sets:set(digraph:vertex()), [digraph:vertex()]) ->
          {[digraph:vertex()], sets:set(digraph:vertex())}.
'digraph_utils:posttraverse'(_, _, _, _) -> error(overlay).
-spec 'digraph_utils:in'(digraph:graph(), digraph:vertex(), [digraph:vertex()]) -> [digraph:vertex()].
'digraph_utils:in'(_, _, _) -> error(overlay).
-spec 'digraph_utils:out'(digraph:graph(), digraph:vertex(), [digraph:vertex()]) -> [digraph:vertex()].
'digraph_utils:out'(_, _, _) -> error(overlay).
