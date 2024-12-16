-module(varenv).

% @doc An environment for variables that cannot be shadowed.
% The env is used for type variables and global functions.

-export([empty/1,
         insert/4,
         insert_if_absent/3,
         lookup/3,
         find/2,
         range/1
        ]).

-export_type([
    t/2
]).

-compile(nowarn_singleton_typevar).
-compile(nowarn_shadow_vars).

-opaque t(K, V) :: {string(), #{ K => V }}.

% Constructs a new, empty varenv.
-spec empty(string()) -> t(_K, _V).
empty(What) -> {What, #{}}.

% Inserts a new binding, an error is thrown if there already exists a binding.
-spec insert(ast:loc(), K, V, t(K, V)) -> t(K, V).
insert(Loc, Key, Val, {What, Map}) ->
    NewMap =
        case maps:find(Key, Map) of
            {ok, _} -> errors:name_error(Loc, "~s ~w already defined", [What, Key]);
            error -> Map#{ Key => Val}
        end,
    {What, NewMap}.

-spec insert_if_absent(K, V, t(K, V)) -> t(K, V).
insert_if_absent(Key, Val, {What, Map}) ->
    NewMap =
        case maps:find(Key, Map) of
            {ok, _} -> Map;
            error -> Map#{ Key => Val}
        end,
    {What, NewMap}.

-spec range(t(_K, V)) -> [V].
range({_, Map}) ->
    lists:map(fun({_, V}) -> V end, maps:to_list(Map)).

% Looks up a variable, undefined variables cause an error.
-spec lookup(ast:loc(), K, t(K, V)) -> V.
lookup(Loc, Key, Env = {What,_ }) ->
    case find(Key, Env) of
        error -> errors:name_error(Loc, "Undefined ~s ~w", [What, Key]);
        {ok, X} -> X
    end.

% Looks up a variable or returns none
-spec find(K, t(K, V)) -> t:opt(V).
find(Key, {_, Map}) -> maps:find(Key, Map).
