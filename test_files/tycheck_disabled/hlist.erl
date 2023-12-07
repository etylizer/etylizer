-module(hlist).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

% These hlist types have to be become builtins. They can't be modelled in erlangs type system.

% The following types encode lists with a fixed number of elements. We could use tuples for this
% purpose, but the erlang API use such lists in some places.
%-type hlist() :: [].
%-type hlist(T) :: [T].
%-type hlist(T, U) :: [T | U].
-type hlist(T, U, V) :: [T | U | V].

% The following types encode lists with a fixed prefix, followed by an arbitrary number of elements.
%-type hlist_many(T, U) :: [T | U]. % one T, then arbitrarily many Us
-type hlist_many(T, U, V) :: [T | U | V]. % one T, one V, then arbitrarily many Vs

-spec foo(hlist(integer(), string(), integer())) -> integer().
foo(L) ->
    case L of
        [X, _, Y] -> X + Y
    end.

-spec bar(hlist_many(integer(), string(), integer())) -> list(integer()).
bar(L) ->
    case L of
        [X, _ | Y] -> [X | Y]
    end.

my_test() ->
    ?assertEqual(3, foo([1, "foo", 2])),
    ?assertEqual([1,2,3,4], bar([1, "foo", 2, 3, 4])),
    ?assertEqual([1], bar([1, "foo"])).
