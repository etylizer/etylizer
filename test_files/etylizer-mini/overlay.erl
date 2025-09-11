-module(overlay).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

-spec 'string:find' (string(), string(), string:direction()) -> string() | nomatch.
'string:find'(_, _, _) -> error(overlay).

-spec 'string:replace' (string(), string(), string()) -> [string()].
'string:replace'(_, _, _) -> error(overlay).

-spec 'string:replace' (string(), string(), string(), string:direction() | all) -> [string()].
'string:replace'(_, _, _, _) -> error(overlay).

-spec 'filename:join'([string()]) -> string().
'filename:join'(_) -> error(overlay).

-spec 'filename:join'(string(), string()) -> string().
'filename:join'(_, _) -> error(overlay).

-spec 'filename:basename'(string(), string()) -> string().
'filename:basename'(_, _) -> error(overlay).

-spec 'lists:map'(fun((A) -> B), [A]) -> [B].
'lists:map'(_, _) -> error(overlay).

-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).

-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(overlay).

-spec 'lists:keyfind'(Key :: term(), N :: pos_integer(), [Tuple]) -> Tuple | false.
'lists:keyfind'(_, _, _) -> error(overlay).

-spec 'lists:ukeysort'(1, [{K, V}]) -> [{K, V}].
'lists:ukeysort'(1, _) -> error(overlay).

-spec 'maps:from_list'
(list()) -> map();
(list({Key, Value})) -> #{Key => Value}.
'maps:from_list'(_) -> error(overlay).

-spec 'maps:to_list'
(map()) -> list() ;
(#{Key => Value}) -> [{Key, Value}].
'maps:to_list'(_) -> error(overlay).

% -type deepList(A) :: [A | deepList(A)].
% -spec 'lists:flatten'(deepList(A)) -> [A].
% 'lists:flatten'(_) -> error(overlay).

-spec 'erlang:element'
    (2, {_A, B}) -> B;
    (2, {_A, B, _C}) -> B;
    (2, {_A, B, _C, _D}) -> B;
    (2, {_A, B, _C, _D, _E}) -> B;
    (2, {_A, B, _C, _D, _E, _F}) -> B;
    (2, {_A, B, _C, _D, _E, _F, _G}) -> B;
    (2, {_A, B, _C, _D, _E, _F, _G, _H}) -> B.
'erlang:element'(_, {_A, B}) -> B;
'erlang:element'(_, {_A, B, _C}) -> B;
'erlang:element'(_, {_A, B, _C, _D}) -> B;
'erlang:element'(_, {_A, B, _C, _D, _E}) -> B;
'erlang:element'(_, {_A, B, _C, _D, _E, _F}) -> B;
'erlang:element'(_, {_A, B, _C, _D, _E, _F, _G}) -> B;
'erlang:element'(_, {_A, B, _C, _D, _E, _F, _G, _H}) -> B.
