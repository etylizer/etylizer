-module(paper_ifl).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec last_day_of_the_month(Year, Month) -> LastDay when
    Year :: non_neg_integer(),
    Month :: 1..12,
    LastDay :: 28..31.
last_day_of_the_month(Y, M) when is_integer(Y), Y >= 0 ->
    last_day_of_the_month1(Y, M).

-spec last_day_of_the_month1(non_neg_integer(),1..12) -> 28..31.
last_day_of_the_month1(_, 4) -> 30;
last_day_of_the_month1(_, 6) -> 30;
last_day_of_the_month1(_, 9) -> 30;
last_day_of_the_month1(_,11) -> 30;
last_day_of_the_month1(Y, 2) ->
    case is_leap_year(Y) of
        true -> 29;
        _    -> 28
    end;
last_day_of_the_month1(_, M) when is_integer(M), M > 0, M < 13 ->
    31.

-spec is_leap_year(Year) -> boolean() when
    Year :: non_neg_integer().
is_leap_year(Y) when is_integer(Y), Y >= 0 ->
    is_leap_year1(Y).

% TODO too slow
-spec is_leap_year1(non_neg_integer()) -> boolean().
is_leap_year1(Year) when Year rem 4 =:= 0, Year rem 100 > 0 ->
    true;
is_leap_year1(Year) when Year rem 400 =:= 0 ->
    true;
is_leap_year1(_) -> false.




-spec lookup(K, [{K, V}]) -> 'none' | V.
% not possible to type check?
% also TODO tuple_any to implement?
%%-spec lookup(Key, List) -> 'none' | tuple() when
%%    Key :: term(),
%%    List :: [term()].
lookup(_, []) -> none;
lookup(K, [{K, V}|_]) -> V;
lookup(K, [_ | KVs])-> lookup(K, KVs).

-spec find_ok() -> any().
find_ok() -> 1 = lookup(0, [{0, 1}]).

-spec find_fail() -> any().
find_fail() -> "s" = lookup(0, [{0, 1}]).


