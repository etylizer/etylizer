-module(etylizer_overlay).

-compile([export_all, nowarn_export_all]).



% TODO ets:update_counter could be improved with an intersection type
-spec 'ets:update_counter' (reference() | atom(), term(), integer() | {integer(), integer()}) -> integer().
'ets:update_counter'(_, _, _) -> error(badarg).

% TODO stdlib list overlays
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(badarg).
-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(badarg).

% more precise filtermap spec needed for ty_map:split_into_associations
% basically a replacement for list comprehensions with filters
-spec 'lists:filtermap'(fun((T) -> boolean()), [T]) -> [T]
                ; (fun((T) -> {true, U} | false), [T]) -> [U]
                ; (fun((T) -> {true, U} | boolean()), [T]) -> [T | U].
'lists:filtermap'(_, _) -> error(badarg).

-spec 'lists:usort'
  (fun((T, T) -> boolean()), nonempty_list(T)) -> nonempty_list(T);
  (fun((T, T) -> boolean()), list(T)) -> list(T).
'lists:usort'(_, _) -> error(overlay).

-spec 'lists:usort'
  (nonempty_list(T)) -> nonempty_list(T);
  (list(T)) -> list(T).
'lists:usort'(_) -> error(overlay).

-spec 'lists:keysort'(1, [{K, V}]) -> [{K, V}].
'lists:keysort'(1, _) -> error(overlay).

-spec 'lists:reverse'
  (nonempty_list(T)) -> nonempty_list(T);
  (list(T)) -> list(T).
'lists:reverse'(_) -> error(overlay).


-spec 'erlang:length'
    (list(_)) -> non_neg_integer();
    (nonempty_list(_)) -> pos_integer().
'erlang:length'(_List) -> error(overlay).

-spec 'erlang:tl'(nonempty_list(A)) -> A.
'erlang:tl'(_List) -> error(overlay).

-spec 'erlang:hd'(nonempty_list(A)) -> A.
'erlang:hd'(_List) -> error(overlay).

-spec 'lists:flatten'(DeepList) -> [A] when DeepList :: [A | DeepList].
'lists:flatten'(_) -> error(overlay).

% TODO bdd.hrl:espresso_split_line_into_elements_and_result/1: why is string() not compatible with [chardata()]?
-spec 'string:split'(string(), string()) -> [string()].
'string:split'(_, _) -> error(badarg).
-spec 'string:split'(string(), string(), all) -> [string()].
'string:split'(_, _, _) -> error(badarg).
-spec 'string:slice'(string(), non_neg_integer(), non_neg_integer()) -> string().
'string:slice'(_, _, _) -> error(badarg).
-spec 'os:cmd'(string()) -> string().
'os:cmd'(_) -> error(badarg).
-spec 'file:write_file'(string(), string()) -> _.
'file:write_file'(_, _) -> error(badarg).

-spec 'maps:get'(Key, #{Key => Value}) -> Value.
'maps:get'(_, _) -> error(badarg).
-spec 'maps:put'(Key, Value, #{Key => Value}) -> #{Key => Value}.
'maps:put'(_, _, _) -> error(badarg).
-spec 'maps:is_key'(Key, #{Key => _Value}) -> boolean().
'maps:is_key'(_, _) -> error(badarg).
-spec 'maps:from_list'([{Key, Value}]) -> #{Key => Value}.
'maps:from_list'(_) -> error(badarg).
-spec 'maps:to_list'(#{Key => Value}) -> list({Key, Value}).
'maps:to_list'(_) -> error(badarg).
