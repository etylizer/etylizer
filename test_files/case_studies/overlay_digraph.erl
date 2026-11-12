-module(overlay_digraph).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of digraph.erl that have none upstream.

% upstream's commented-out spec, and error
-spec 'digraph:check_type'([digraph:d_type()], digraph:d_protection(), [{cyclic, boolean()}]) ->
          {digraph:d_protection(), [{cyclic, boolean()}]} | error.
'digraph:check_type'(_, _, _) -> error(overlay).
-spec 'digraph:collect_elems'([{term(), term()}], ets:table(), pos_integer()) -> [term()].
'digraph:collect_elems'(_, _, _) -> error(overlay).
-spec 'digraph:collect_elems'([{term(), term()}], ets:table(), pos_integer(), [term()]) -> [term()].
'digraph:collect_elems'(_, _, _, _) -> error(overlay).
-spec 'digraph:other_edge_exists'(digraph:graph(), digraph:edge(), digraph:vertex(), digraph:vertex()) -> boolean().
'digraph:other_edge_exists'(_, _, _, _) -> error(overlay).
-spec 'digraph:prune_short_path'(integer(), integer()) -> short | ok.
'digraph:prune_short_path'(_, _) -> error(overlay).
-spec 'digraph:one_path'([digraph:vertex()], digraph:vertex(), [{[digraph:vertex()], [digraph:vertex()]}],
                         [digraph:vertex()], [digraph:vertex()], integer(), digraph:graph(), integer()) ->
          [digraph:vertex(), ...] | false.
'digraph:one_path'(_, _, _, _, _, _, _, _) -> error(overlay).
