-module(overlay_proplists_corrected).
-compile([export_all, nowarn_export_all]).

% Corrected specs of proplists.erl: calls use them, the functions are checked against
% these and their specs upstream.

-spec 'proplists:property'(T) -> T | atom().
'proplists:property'(_) -> error(overlay).
-spec 'proplists:compact'([T]) -> [T | atom()].
'proplists:compact'(_) -> error(overlay).
% Leftmost association first: #{Shorthand => true, Key => Value} with Shorthand :: atom() maps
% every atom key to true, to_map([{b, 1}]) is #{b => 1}.
-spec 'proplists:to_map'([term()]) -> #{term() => term()}.
'proplists:to_map'(_) -> error(overlay).
% A value that is an improper list: ++ raises badarg.
-spec 'proplists:append_values'(term(), [etylizer:without(term(), {term(), nonempty_improper_list(term(), etylizer:without(term(), list()))})]) -> [term()].
'proplists:append_values'(_, _) -> error(overlay).
% For a list of pairs the value is one of the list's values or the default.
-spec 'proplists:get_value'(K, [{K, V}], D) -> V | D; (term(), [term()], D) -> term() | D.
'proplists:get_value'(_, _, _) -> error(overlay).
