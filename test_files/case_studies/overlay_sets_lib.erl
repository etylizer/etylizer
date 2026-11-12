-module(overlay_sets_lib).
-compile([export_all, nowarn_export_all]).

% Library specs for sets.erl.

% OTP: (term(), [term()], term()) -> term(). For a list of pairs the value is one of
% the list's values or the default.
-spec 'proplists:get_value'(K, [{K, V}], D) -> V | D;
                           (term(), [term()], D) -> term() | D.
'proplists:get_value'(_, _, _) -> error(overlay).

% OTP: (pos_integer(), tuple()) -> term() and (tuple()) -> [term()]; a segment has one element type.
-spec 'erlang:element'(pos_integer(), overlay_sets:seg(E)) -> [E];
                      (pos_integer(), tuple()) -> term().
'erlang:element'(_, _) -> error(overlay).
-spec 'erlang:tuple_to_list'(overlay_sets:seg(E)) -> [[E]];
                            (tuple()) -> [term()].
'erlang:tuple_to_list'(_) -> error(overlay).
