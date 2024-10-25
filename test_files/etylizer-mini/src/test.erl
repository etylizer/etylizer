-module(test).

% @doc An environment for variables that cannot be shadowed.
% The env is used for type variables and global functions.

-export([insert/3]).

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

% insert/3 fails to type check with the first spec, but succeeds with the second.
% But if we copy the whole test.erl file to the toplevel directory and the invoke
%
% $./ety --build --force --level debug test.erl
%
% type checking with the first spec works (as expected). There must be some
% global state being involved.
-spec insert(K, V, t1(K, V)) -> t1(K, V).
%-spec insert(K, V, #{ K => V }) -> #{ K => V }.
insert(Key, Val, Map) ->
    %case maps:find(Key, Map) of
    case maps_find(Key, Map) of
        {ok, _} -> #{};
        error -> Map#{ Key => Val}
    end.
