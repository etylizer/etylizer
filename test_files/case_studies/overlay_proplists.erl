-module(overlay_proplists).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

% Specs for the functions of proplists.erl that have none upstream.

-spec 'proplists:get_keys'([term()], sets:set(term())) -> sets:set(term()).
'proplists:get_keys'(_, _) -> error(overlay).
-spec 'proplists:substitute_aliases_1'([{term(), term()}], term()) -> term().
'proplists:substitute_aliases_1'(_, _) -> error(overlay).
-spec 'proplists:substitute_negations_1'([{term(), term()}], term()) -> term().
'proplists:substitute_negations_1'(_, _) -> error(overlay).
-spec 'proplists:expand_0'([{proplists:property(), [term()]}], [term()]) -> [term()].
'proplists:expand_0'(_, _) -> error(overlay).
-spec 'proplists:expand_1'(proplists:property(), [term()], [term()]) -> [term()].
'proplists:expand_1'(_, _, _) -> error(overlay).
-spec 'proplists:expand_2'(term(), proplists:property(), [term()], [term()]) -> [term()].
'proplists:expand_2'(_, _, _, _) -> error(overlay).
-spec 'proplists:expand_3'(term(), proplists:property(), proplists:property(), [term()], [term()]) -> [term()].
'proplists:expand_3'(_, _, _, _, _) -> error(overlay).
-spec 'proplists:key_uniq'([{proplists:property(), [term()]}]) -> [{proplists:property(), [term()]}].
'proplists:key_uniq'(_) -> error(overlay).
-spec 'proplists:key_uniq_1'(proplists:property(), [{proplists:property(), [term()]}]) -> [{proplists:property(), [term()]}].
'proplists:key_uniq_1'(_, _) -> error(overlay).
-spec 'proplists:flatten'([[A]]) -> [A]; ([etylizer:without(A, maybe_improper_list())]) -> [A]. % top-level flatten only
'proplists:flatten'(_) -> error(overlay).
-spec 'proplists:apply_stages'([term()], [({'aliases', [{term(), term()}]} | {'negations', [{term(), term()}]} | {'expand', [{proplists:property(), [term()]}]})]) -> [term()].
'proplists:apply_stages'(_, _) -> error(overlay).
-spec 'proplists:split'([term()], #{term() => [term()]}, [term()]) -> {#{term() => [term()]}, [term()]}.
'proplists:split'(_, _, _) -> error(overlay).
-spec 'proplists:maps_prepend'(term(), term(), #{term() => [term()]}) -> #{term() => [term()]}.
'proplists:maps_prepend'(_, _, _) -> error(overlay).
