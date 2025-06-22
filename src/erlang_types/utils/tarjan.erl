-module(tarjan).
-export([scc/1]).

-type graph() :: tuple(). % array of lists representing adjacency lists
-type vertex() :: integer().
-type scc_id() :: integer().
-type scc_result() :: {[{scc_id(), [vertex()]}], #{(vertex()) => scc_id()}}.

-spec scc(graph()) -> scc_result().
scc(Graph) ->
    InitialState = #{
        ixes => maps:new(),
        lows => maps:new(),
        stack => [],
        num => 1,
        sccs => [],
        next_scc => 1
    },
    Vertices = lists:seq(0, tuple_size(Graph) - 1),
    FinalState = roots(Graph, InitialState, Vertices),
    SCCMap = maps:get(ixes, FinalState),
    {
        maps:get(sccs, FinalState),
        SCCMap
    }.

roots(_Graph, State, []) -> State;
roots(Graph, State, [V|Vs]) ->
    case maps:is_key(V, maps:get(ixes, State)) of
        true -> roots(Graph, State, Vs);
        false -> 
            NewState = from_root(Graph, State, V),
            roots(Graph, NewState, Vs)
    end.

from_root(Graph, State, V) ->
    Me = maps:get(num, State),
    NewState0 = State#{
        ixes => maps:put(V, -Me, maps:get(ixes, State)),
        lows => maps:put(V, Me, maps:get(lows, State)),
        stack => [V | maps:get(stack, State)],
        num => Me + 1
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
                        ixes => Ixes1,
                        stack => Bs,
                        sccs => [{N, This} | maps:get(sccs, NewState1)],
                        next_scc => N + 1
                    }
            end
    end.

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