-module(ast_traverse).

% @doc Typed traversals of the internal AST (see ast.erl).
%
% utils:everything/2 traverses arbitrary terms, so its callback only ever sees term().
% This module provides a typed replacement for the AST:
%
% - everything/2 is a generic query, just like utils:everything/2. It does not know the
%   structure of the AST; that is described by the type external_types:subterm() alone.
%   The callback receives such a subterm and can match on it precisely.

-export([
    everything/2,
    subterms/1
]).

%% ---------------------------------------------------------------------------
%% Queries
%% ---------------------------------------------------------------------------

% Collects all results R where the given function returns {ok, R} or {rec, R} for one of
% the given terms or a subterm of them. {ok, R} collects R and does not descend into the
% term; {rec, R} collects R and descends; error just descends.
% Subterms are visited in the order in which they appear in the AST.
-spec everything(fun((external_types:subterm()) -> {ok, R} | {rec, R} | error),
                 [external_types:subterm()]) -> [R].
everything(F, Terms) ->
    utils:everything(fun subterms/1, F, Terms).

% The direct subterms of a term: the elements of a list and the components of a tuple.
% This function does not know the AST. That it type checks proves that
% external_types:subterm() is closed, so the function given to everything/2 is only ever
% applied to such a subterm.
-spec subterms(external_types:subterm()) -> [external_types:subterm()].
subterms({attribute, Loc, compile, _}) -> [attribute, Loc, compile];
subterms([H | T]) -> [H | subterms(T)];
subterms({A}) -> [A];
subterms({A, B}) -> [A, B];
subterms({A, B, C}) -> [A, B, C];
subterms({A, B, C, D}) -> [A, B, C, D];
subterms({A, B, C, D, E}) -> [A, B, C, D, E];
subterms({A, B, C, D, E, F}) -> [A, B, C, D, E, F];
subterms({A, B, C, D, E, F, G}) -> [A, B, C, D, E, F, G];
subterms(_) -> [].
