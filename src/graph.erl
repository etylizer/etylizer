-module(graph).

-export([with_graph/1, add_vertex/2, add_edge/3, out_neighbours/2,
         strong_components/1, topsort/1, to_list/2]).

-export_type([graph/1]).

-type digraph(_V) :: digraph:graph().
-type table(_V) :: ets:table().
% A graph consists of a diagraph and a table mapping extern vertices of
% type V to vertices used by the digraph
-type graph(V) :: {digraph(V), table(V)}.

-spec with_graph(fun((graph(_V)) -> T)) -> T.
with_graph(F) ->
    G = digraph:new(),
    Tab = ets:new(graph_table, []),
    Graph = {G, Tab},
    try F(Graph)
    after
        digraph:delete(G),
        ets:delete(Tab)
    end.

-spec add_vertex(graph(V), V) -> ok.
add_vertex({G, Tab}, ExternV) ->
    InternV = digraph:add_vertex(G),
    InternV = digraph:add_vertex(G, InternV, ExternV),
    ets:insert(Tab, {ExternV, InternV}),
    ok.

-spec get_intern(table(V), V) -> digraph:vertex().
get_intern(Tab, V) ->
    case ets:lookup(Tab, V) of
        [] -> errors:bug("no such vertex: ~w", V);
        [{_, InternV}] -> InternV;
        _ -> errors:bug("more than one vertex found for ~w", V)
    end.

-spec get_extern(digraph(V), digraph:vertex()) -> V.
get_extern(G, InternV) ->
    case digraph:vertex(G, InternV) of
        false -> errors:bug("no such vertex: ~w", InternV);
        {_, ExternV} -> ExternV
    end.

% add_edge(G, V1, V2) adds an edge from V1 to V2 to graph G. Does nothing if
% such an edge already exists.
-spec add_edge(graph(V), V, V) -> ok.
add_edge({G, Tab}, ExternSrc, ExternTgt) ->
    InternSrc = get_intern(Tab, ExternSrc),
    InternTarget = get_intern(Tab, ExternTgt),
    ExistingTargets = digraph:out_neighbours(G, InternSrc),
    case lists:member(InternTarget, ExistingTargets) of
        true -> ok;
        false ->
            case digraph:add_edge(G, InternSrc, InternTarget) of
                {error, _} ->
                    errors:bug("cannot add edge to graph");
                _ -> ok
            end
    end.

-spec out_neighbours(graph(V), V) -> [V].
out_neighbours({G, Tab}, V) ->
    InternV = get_intern(Tab, V),
    L = digraph:out_neighbours(G, InternV),
    lists:map(fun(Out) -> get_extern(G, Out) end, L).

-spec strong_components(graph(V)) -> sets:set(sets:set(V)).
strong_components({G, _}) ->
    LL = digraph_utils:strong_components(G),
    sets:from_list(lists:map(
      fun(L) ->
              sets:from_list(lists:map(fun(InternV) -> get_extern(G, InternV) end, L))
      end,
      LL)).

-spec topsort(graph(V)) -> [V] | cyclic.
topsort({G, _}) ->
    case digraph_utils:topsort(G) of
        false -> cyclic;
        L ->
            lists:map(fun(InternV) -> get_extern(G, InternV) end, L)
    end.

-spec to_list(graph(V), fun((V) -> string())) -> list({V, list(V)}).
to_list(G = {_, Tab}, F) ->
    ets:foldl(
      fun({V, _}, Acc) -> [ {F(V), lists:map(F, out_neighbours(G, V))} | Acc ] end,
      [],
      Tab).
