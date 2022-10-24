-module(hlist_fail).

-compile(export_all).
-compile(nowarn_export_all).

% These hlist types have to be become builtins. They can't be modelled in erlangs type system.

% The following types encode lists with a fixed number of elements. We could use tuples for this
% purpose, but the erlang API use such lists in some places.
-type hlist() :: [].
-type hlist(T) :: [T].
-type hlist(T, U) :: [T | U].
-type hlist(T, U, V) :: [T | U | V].

% The following types encode lists with a fixed prefix, followed by an arbitrary number of elements.
-type hlist_many(T, U) :: [T | U]. % one T, then arbitrarily many Us
-type hlist_many(T, U, V) :: [T | U | V]. % one T, one V, then arbitrarily many Vs

-spec foo(hlist(integer(), string(), integer())) -> integer().
foo(L) ->
    case L of
        [_, X, _] -> X
    end.
