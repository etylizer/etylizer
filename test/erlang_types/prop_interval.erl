-module(prop_interval).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").


-export([limited_interval/0]).

limited_interval() ->
  ?SIZED(Size, limited_interval(Size)).

limited_interval(Size) when Size =< 1 ->
  frequency([
    {1, ?LAZY(ty_interval:any())},
    {1, ?LAZY(ty_interval:empty())},
    {2, ?LAZY(?LET(SingleInt, integer(), ty_interval:interval(SingleInt, SingleInt)))},
    {8, ?LAZY(?LET({From, To}, {integer(), integer()}, ty_interval:interval(From, To)))}
  ]);
limited_interval(Size) ->
  frequency([
    {3, ?LAZY(?LET({A, B}, {limited_interval(Size div 2), limited_interval(Size div 2)}, ty_interval:union(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_interval(Size div 2), limited_interval(Size div 2)}, ty_interval:intersect(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_interval(Size div 2), limited_interval(Size div 2)}, ty_interval:diff(A, B)))  },
    {2, ?LAZY(?LET(CompoundInt, limited_interval(Size - 1), ty_interval:negate(CompoundInt)))  }
  ]).


% syntactical properties

% if any_int in list then list size == 1
prop_any_int_only_once() -> ?FORALL(X, limited_interval(), ?IMPLIES(lists:member(any_int, X), X =:= [any_int])).

% 2) there is at most only one left and only one right
prop_at_most_one_left_right() ->
  ?FORALL(X, limited_interval(),
    conjunction([
      {left, begin
        {P, _} = lists:partition(fun({left, _}) -> true; (_) -> false end, X),
        length(P) == 0 orelse length(P) == 1
      end},
      {right, begin
        {Z, _} = lists:partition(fun({right, _}) -> true; (_) -> false end, X),
        length(Z) == 0 orelse length(Z) == 1
      end}
    ])
).

% TODO
% 3) sorted
%  3.1) there is no left after any range or right
%  3.2) there is no range after any right
%  3.3) there is no right before any range or left
%  3.4) there is no range before any left
%  3.5) for any two adjacent ranges: ranges do not overlap
%  3.6) if left and next range: left smaller than range left
%  3.7) if left and next right: left smaller than right
%  3.8) if right and before range: right bigger than range right
%  3.9) if right and before left: right bigger than left

% semantic properties

prop_interval_order_le_transitive() ->
  ?FORALL({X, Y, Z}, {limited_interval(), limited_interval(), limited_interval()},
    ?IMPLIES(ty_interval:compare(X, Y) =:= -1 andalso ty_interval:compare(Y,Z) =:= -1, ty_interval:compare(X, Z) =:= -1)
  ).
