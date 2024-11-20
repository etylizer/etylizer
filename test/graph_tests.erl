-module(graph_tests).

-include_lib("eunit/include/eunit.hrl").

simple_graph_test() ->
    graph:with_graph(fun test_graph_01/1),
    graph:with_graph(fun test_graph_02/1).

-spec test_graph_01(graph:graph(string())) -> ok.
test_graph_01(G) ->
    graph:add_vertex(G, "V0"),
    graph:add_vertex(G, "V1"),
    graph:add_vertex(G, "V2"),
    graph:add_vertex(G, "V3"),
    graph:add_vertex(G, "V4"),
    graph:add_vertex(G, "ISOLATED"),
    % V0 -> V1 -> V2 -> V3 -> V4    ISOLATED
    %       ^           |
    %       +-----------+
    graph:add_edge(G, "V0", "V1"),
    graph:add_edge(G, "V1", "V2"),
    graph:add_edge(G, "V2", "V3"),
    graph:add_edge(G, "V3", "V1"),
    graph:add_edge(G, "V3", "V4"),
    ?assertEqual([], graph:out_neighbours(G, "ISOLATED")),
    ?assertEqual(["V4", "V1"], graph:out_neighbours(G, "V3")),
    ?assertEqual(
       sets:from_list([
         sets:from_list(["V0"], [{version, 2}]),
         sets:from_list(["V1", "V2", "V3"], [{version, 2}]),
         sets:from_list(["V4"], [{version, 2}]),
         sets:from_list(["ISOLATED"], [{version, 2}])
        ], [{version, 2}]),
       graph:strong_components(G)
       ).

-spec test_graph_02(graph:graph(string())) -> ok.
test_graph_02(G) ->
    graph:add_vertex(G, "V0"),
    graph:add_vertex(G, "V1"),
    graph:add_vertex(G, "V2"),
    graph:add_vertex(G, "V3"),
    graph:add_vertex(G, "V4"),
    % V0 -> V1 -> V3 -> V4
    % |                 ^
    % +--> V2 ----------+
    graph:add_edge(G, "V0", "V1"),
    graph:add_edge(G, "V0", "V2"),
    graph:add_edge(G, "V1", "V3"),
    graph:add_edge(G, "V3", "V4"),
    graph:add_edge(G, "V2", "V4"),
    L = graph:topsort(G),
    ?assert(L == ["V0","V1","V2","V3","V4"] orelse
            L == ["V0","V1","V3","V2","V4"] orelse
            L == ["V0","V2","V1","V3","V4"]).
