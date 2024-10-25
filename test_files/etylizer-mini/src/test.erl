-module(varenv).

% @doc An environment for variables that cannot be shadowed.
% The env is used for type variables and global functions.

-export([insert/3
        ]).

-export_type([
    t1/2
]).

-compile(nowarn_singleton_typevar).
-compile(nowarn_shadow_vars).

-opaque t1(K, V) :: #{ K => V }.

% ORIGINAL spec
% -spec find(Key, #{Key => Value, term() => term()}) -> {ok, Value} | error
-spec maps_find(K, #{ K => V}) -> {ok, V} | error.
maps_find(K, M) -> maps_find(K, M).

% Inserts a new binding, an error is thrown if there already exists a binding.
-spec insert(K, V, t1(K, V)) -> t1(K, V).
%-spec insert(K, V, #{ K => V }) -> #{ K => V }.
insert(Key, Val, Map) ->
    case maps_find(Key, Map) of
        {ok, _} -> #{};
        error -> Map#{ Key => Val}
    end.
