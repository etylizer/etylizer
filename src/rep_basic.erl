-module(rep_basic).

% -export([union/2, intersect/2, diff/2, eq/2]).
% -export([finite/1, cofinite/1]).
% -export([empty/0, any/0]).
% -export([eval/1]).
% -export([is_empty/1]).


% FIXME HACK
% want to pattern match against gb_set:new()
-define(INTERNAL, {0, nil}).
-define(EMPTY, {?INTERNAL, finite}).
-define(ANY,   {?INTERNAL, cofinite}).


empty() -> ?EMPTY.
any() -> ?ANY.

eval({Atoms, Tag}) ->
  Union = {union, [lists:map(fun(Atom) -> {singleton, Atom} end, gb_sets:to_list(Atoms))]},
  case Tag of
    finite -> Union;
    _ -> {negation, Union}
  end.

finite([]) -> any();
finite([X | Xs]) -> intersect({gb_sets:from_list([X]), finite}, finite(Xs)).
cofinite(ListOfBasic) -> {gb_sets:from_list(ListOfBasic), cofinite}.

negate({S, finite}) -> {S, cofinite};
negate({S, cofinite}) -> {S, finite}.

intersect(_, ?EMPTY) -> ?EMPTY;
intersect(?EMPTY, _) -> ?EMPTY;
intersect(?ANY, S) -> S;
intersect(S, ?ANY) -> S;
intersect(S = {_, cofinite}, T = {_, finite}) -> intersect(T, S);
intersect({S, finite}, {T, finite}) ->
  {gb_sets:intersection(S, T), finite};
intersect({S, finite}, {T, cofinite}) ->
  {gb_sets:difference(S, T), finite};
intersect({S, cofinite}, {T, cofinite}) ->
  {gb_sets:union(S,T), cofinite}.

union(S,T) -> negate(intersect(negate(S), negate(T))).

diff(S,T) -> intersect(S, negate(T)).

eq({_, finite},{_, cofinite}) -> false;
eq({_, cofinite},{_, finite}) -> false;
eq({S, _},{T, _}) -> gb_sets:is_subset(S,T) andalso gb_sets:is_subset(T,S).

is_empty(Rep) ->
  case Rep of
    ?EMPTY -> true;
    _ -> false
  end.