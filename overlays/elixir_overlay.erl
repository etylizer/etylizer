-module(elixir_overlay).

-compile([export_all, nowarn_export_all]).

% Elixir Enum.map/2: overloaded for lists and maps.
% The native Elixir spec is (Enumerable.t(), (any() -> any())) -> list(),
% which loses all type information. This overlay provides precise types.
-spec 'Elixir.Enum:map'([A], fun((A) -> B)) -> [B];
                        (#{K => V}, fun(({K, V}) -> R)) -> [R].
'Elixir.Enum:map'(_, _) -> error(overlay).

% Elixir Enum.filter/2
-spec 'Elixir.Enum:filter'([A], fun((A) -> boolean())) -> [A].
'Elixir.Enum:filter'(_, _) -> error(overlay).

% Elixir Enum.all?/2
-spec 'Elixir.Enum:all?'([A], fun((A) -> boolean())) -> boolean().
'Elixir.Enum:all?'(_, _) -> error(overlay).

% Elixir Enum.reverse/1
-spec 'Elixir.Enum:reverse'([A]) -> [A].
'Elixir.Enum:reverse'(_) -> error(overlay).

% Elixir List.foldl/3
-spec 'Elixir.List:foldl'([T], Acc, fun((T, Acc) -> Acc)) -> Acc.
'Elixir.List:foldl'(_, _, _) -> error(overlay).

% Elixir List.to_tuple/1
-spec 'Elixir.List:to_tuple'([term()]) -> tuple().
'Elixir.List:to_tuple'(_) -> error(overlay).

% Elixir Tuple.to_list/1
-spec 'Elixir.Tuple:to_list'(tuple()) -> [term()].
'Elixir.Tuple:to_list'(_) -> error(overlay).
