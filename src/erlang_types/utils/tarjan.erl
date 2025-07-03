-module(tarjan).
-export([
  reverse_graph/1,
  condense/1,
  dfs/1,
  scc/1
]).

-type graph()      :: tuple(). % array of lists representing adjacency lists
-type vertex()     :: integer().
-type scc_id()     :: integer().
-type scc_result() :: {[{scc_id(), [vertex()]}], #{vertex() => scc_id()}}.
-type state()      :: #{
                      ixes     => #{vertex() => integer()},
                      lows     => #{vertex() => integer()},
                      stack    => [vertex()],
                      num      => integer(),
                      sccs     => [{scc_id(), [vertex()]}],
                      next_scc => integer()
                     }.

-spec scc(graph()) -> scc_result().
scc(Graph) ->
  InitialState = #{
    ixes      => maps:new(),
    lows      => maps:new(),
    stack     => [],
    num       => 1,
    sccs      => [],
    next_scc  => 1
  },
  Vertices = lists:seq(0, tuple_size(Graph) - 1),
  FinalState = roots(Graph, InitialState, Vertices),
  SCCMap = maps:get(ixes, FinalState),
  {
    maps:get(sccs, FinalState),
    SCCMap
  }.

-spec roots(graph(), state(), [vertex()]) -> state().
roots(_Graph, State, []) -> State;
roots(Graph, State, [V|Vs]) ->
  case maps:is_key(V, maps:get(ixes, State)) of
    true  -> roots(Graph, State, Vs);
    false -> 
      NewState = from_root(Graph, State, V),
      roots(Graph, NewState, Vs)
  end.

-spec from_root(graph(), state(), vertex()) -> state().
from_root(Graph, State, V) ->
  Me = maps:get(num, State),
  NewState0 = State#{
    ixes  => maps:put(V, -Me, maps:get(ixes, State)),
    lows  => maps:put(V, Me, maps:get(lows, State)),
    stack => [V | maps:get(stack, State)],
    num   => Me + 1
  },
  Adjacent = element(V + 1, Graph), 
  NewState1 = check_adj(Graph, NewState0, V, Adjacent),
  
  case maps:get(V, maps:get(lows, NewState1)) of
    X when X < Me -> NewState1;
    _ ->
      Stack = maps:get(stack, NewState1),
      {Before, After} = lists:splitwith(fun(Vertex) -> Vertex =/= V end, Stack),
      case After of
        [B | Bs] ->
          This = [B | Before],
          N = maps:get(next_scc, NewState1),
          Ixes1 = lists:foldl(fun(I, M) -> maps:put(I, N, M) end, 
                                maps:get(ixes, NewState1), This),
          NewState1#{
            ixes     => Ixes1,
            stack    => Bs,
            sccs     => [{N, This} | maps:get(sccs, NewState1)],
            next_scc => N + 1
          }
      end
  end.

-spec check_adj(graph(), state(), vertex(), [vertex()]) -> state().
check_adj(_Graph, State, _V, []) -> State;
check_adj(Graph, State, V, [Vprime | Vs]) ->
  case maps:find(Vprime, maps:get(ixes, State)) of
    {ok, I} when I < 0 ->
      Lows = maps:get(lows, State),
      NewLow = min(maps:get(V, Lows), -I),
      Lows1 = maps:put(V, NewLow, Lows),
      check_adj(Graph, State#{lows => Lows1}, V, Vs);
    {ok, _I} ->
      check_adj(Graph, State, V, Vs);
    error ->
      NewState0 = from_root(Graph, State, Vprime),
      Lows = maps:get(lows, NewState0),
      NewLow = min(maps:get(V, Lows), maps:get(Vprime, Lows)),
      Lows1 = maps:put(V, NewLow, Lows),
      NewState1 = NewState0#{lows => Lows1},
      check_adj(Graph, NewState1, V, Vs)
  end.


-spec map(Graph :: #{Node => [Node]}) -> {#{integer() => [integer()]}, #{Node => integer()}} when Node :: term().
map(Graph) ->
  All = lists:usort(lists:flatten([[K, V] || K := V <- Graph])),
  {Max, Mapping} = lists:foldl(fun(Node, {Id, Map}) -> {Id + 1, Map#{Node => Id}} end, {0, #{}}, All),
  Unfilled = #{maps:get(N, Mapping) => [maps:get(NN, Mapping) || NN <- Adj] || N := Adj <- Graph},
  {#{Id => maps:get(Id, Unfilled, []) || Id <- lists:seq(0, Max-1)}, Mapping}.


-spec condense(Graph) -> {SCCs, CondensedGraph} when
    Graph :: #{term() => [term()]},
    SCCs :: #{term() => term()},  % Maps each node to its root (SCC representative)
    CondensedGraph :: #{term() => [term()]}.  % Adjacency list of SCC roots
condense(Graph) ->
  {MappedGraph, Mapping} = map(Graph),
  IdNodeMapping = #{Id => Node || Node := Id <- Mapping},
  G = erlang:list_to_tuple([Adjacency || {_, Adjacency} <- lists:sort(maps:to_list(MappedGraph))]),
  {SCCs, Map} = tarjan:scc(G),

  ScctoN = #{Id => [maps:get(NN, IdNodeMapping) || NN <- Nodes] || {Id, Nodes} <- SCCs},
  NtoScc = #{maps:get(K, IdNodeMapping) => V || K := V <- Map},
  
  % Build a mapping from each node to its root (SCC representative)
  Roots = #{Node => hd(maps:get(Id, ScctoN)) || Node := Id <- NtoScc},
  
  % Get all unique SCC roots
  AllRoots = lists:usort(maps:values(Roots)),
  
  % Initialize the condensed graph with all roots (even those with no edges)
  BaseGraph = maps:from_list([{Root, []} || Root <- AllRoots]),
  
  % Build the condensed graph by:
  % 1. Collecting all edges between different SCCs
  % 2. Avoiding duplicate edges
  CondensedGraph = maps:fold(
      fun(Node, Neighbors, Acc) ->
          Root = maps:get(Node, Roots),
          lists:foldl(
              fun(Neighbor, InnerAcc) ->
                  NeighborRoot = maps:get(Neighbor, Roots),
                  case Root =/= NeighborRoot of
                      true ->
                          % Add edge from Root to NeighborRoot if not already present
                          CurrentEdges = maps:get(Root, InnerAcc),
                          case lists:member(NeighborRoot, CurrentEdges) of
                              false ->
                                  maps:put(Root, [NeighborRoot | CurrentEdges], InnerAcc);
                              true ->
                                  InnerAcc
                          end;
                      false ->
                          InnerAcc
                  end
              end,
              Acc,
              Neighbors
          )
      end,
      BaseGraph,  % Start with all roots already included
      Graph
  ),
  
  {Roots, CondensedGraph}.


-spec dfs(Graph :: #{Node => [Node]}) -> [Node] when Node :: term().
dfs(Graph) ->
    Nodes = maps:keys(Graph),
    Visited = sets:new(),
    {Order, _} = lists:foldl(
        fun(Node, {Acc, VisitedSet}) ->
            case sets:is_element(Node, VisitedSet) of
                false ->
                    {NewAcc, NewVisited} = dfs_visit(Graph, Node, Acc, VisitedSet),
                    {NewAcc, NewVisited};
                true ->
                    {Acc, VisitedSet}
            end
        end,
        {[], Visited},
        Nodes
    ),
    lists:reverse(Order).


-spec dfs_visit(Graph :: #{Node => [Node]}, Node :: term(), Acc :: [Node], VisitedSet :: sets:set(Node)) -> 
    {[Node], sets:set(Node)} when Node :: term().
dfs_visit(Graph, Node, Acc, VisitedSet) ->
    NewVisited = sets:add_element(Node, VisitedSet),
    Neighbors = maps:get(Node, Graph, []),
    {NewAcc, FinalVisited} = lists:foldl(
        fun(Neighbor, {CurrentAcc, CurrentVisited}) ->
            case sets:is_element(Neighbor, CurrentVisited) of
                false ->
                    dfs_visit(Graph, Neighbor, CurrentAcc, CurrentVisited);
                true ->
                    {CurrentAcc, CurrentVisited}
            end
        end,
        {Acc, NewVisited},
        Neighbors
    ),
    {[Node | NewAcc], FinalVisited}.


-spec reverse_graph(Graph :: #{Node => [Node]}) -> #{Node => [Node]} when Node :: term().
reverse_graph(Graph) ->
    Keys = maps:keys(Graph),
    lists:foldl(
        fun(Key, Acc) ->
            case maps:get(Key, Graph) of
                [] -> Acc;  % No need to process nodes with no edges
                Values -> 
                    lists:foldl(
                        fun(Value, InnerAcc) ->
                            case maps:get(Value, InnerAcc, []) of
                                Existing -> InnerAcc#{Value => [Key | Existing]}
                            end
                        end,
                        Acc,
                        Values
                    )
            end
        end,
        #{K => [] || K <- Keys},  % Initialize with all keys pointing to empty lists
        Keys
    ).
