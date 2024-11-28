-module(t).

% @doc Defines *common* types.

-export_type([
    lineno/0, opt/1, opt/2
]).

-type lineno() :: integer().
-type opt(T) :: {ok, T} | error.
-type opt(T, W) :: {ok, T} | {error, W}.
