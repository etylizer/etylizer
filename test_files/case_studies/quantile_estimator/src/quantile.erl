-module(quantile).
-author('Florian Odronitz <odo@mac.com>').

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-export([ceil/1]).
-define(DEBUG, true).
-endif.

-type sample() :: number().
-type samples() :: [sample()].

-export([quantile/2]).
-export([rank_average/2]).

-spec quantile(float(), samples()) -> sample().
quantile(0.0, [First|_]) ->
	First;

quantile(1.0, Samples) ->
	lists:last(Samples);
	
quantile(Quantile, Samples) ->
	case ranks(length(Samples), Quantile) of
		[Index] ->
			lists:nth(Index, Samples);
		[Index1, Index2] ->
			(lists:nth(Index1, Samples) + lists:nth(Index2, Samples)) / 2
	end.

-spec even(integer()) -> boolean().
even(Value) ->
	Value rem 2 =:= 0.

-spec natural(float()) -> boolean().
natural(Value) ->
	(erlang:trunc(Value) * 1.0) =:= Value.

-spec ranks(integer(), float()) -> [integer()] | [integer()|integer()].
ranks(Size, _Quantile) when Size < 1 ->
	throw({error, {Size, size_smaller_one}});

ranks(_Size, Quantile) when Quantile < 0 ->
	throw({error, {Quantile, quantile_smaller_zero}});

ranks(_Size, Quantile) when Quantile > 1 ->
	throw({error, {Quantile, quantile_larger_one}});

ranks(Size, Quantile) ->
	case natural(Size * Quantile) andalso even(Size) of
		true ->
			[round(Size * Quantile), round(Size * Quantile) + 1];
		false ->
			[ceil(Size * Quantile)]
	end.

-spec ceil(float()) -> integer().
ceil(X) ->
    T = erlang:trunc(X),
    case (X - T) of
        Neg when Neg < 0 -> T;
        Pos when Pos > 0 -> T + 1;
        _ -> T
    end.


% TESTS
rank_average(Size, Quantile) ->
	case ranks(Size, Quantile) of
		[V] ->
			V;
		[V1, V2] ->
			(V1 + V2) / 2
	end.


-ifdef(TEST).

quantile_test_() ->
[{foreach, local,
	fun test_setup/0,
	fun test_teardown/1,
	[
		{"test ceil", fun  ceil_test/0}
		,{"test ranks", fun ranks_test/0}
		,{"test natural", fun natural_test/0}
		,{"test even", fun even_test/0}
		,{"test quantiles", fun quantile_test/0}
	]}
].

test_setup() ->
	undefined.

test_teardown(_) ->
	undefined.

ranks_test() ->
	?assertEqual([3], ranks(10, 0.25))
	,?assertEqual([5, 6], ranks(10, 0.5))
	,?assertEqual([8], ranks(10, 0.75))
	,?assertEqual([3], ranks(11, 0.25))
	,?assertEqual([6], ranks(11, 0.5))
	,?assertEqual([9], ranks(11, 0.75)).

natural_test() ->
	?assertEqual(true, natural(10.0))
	,?assertEqual(true, natural(-10.0))
	,?assertEqual(false, natural(10.1))
	,?assertEqual(false, natural(-10.1)).

even_test() ->
	?assertEqual(true, even(10))
	,?assertEqual(true, even(-10))
	,?assertEqual(false, even(11))
	,?assertEqual(false, even(-11)).

ceil_test() ->
	?assertEqual(1, ceil(1.0))
	,?assertEqual(2, ceil(1.1))
	,?assertEqual(2, ceil(1.8))
	,?assertEqual(-1, ceil(-1.8))
	,?assertEqual(-1, ceil(-1.1)).

quantile_test() ->
	Samples1 = [3.0, 6.0, 7.0, 8.0, 8.0, 10.0, 13.0, 15.0, 16.0, 20.0]
	,?assertEqual(7.0, quantile(1/4, Samples1))
	,?assertEqual(9.0, quantile(1/2, Samples1))
	,?assertEqual(15.0, quantile(3/4, Samples1))
	,Samples2 = [3.0, 6.0, 7.0, 8.0, 8.0, 9.0, 10.0, 13.0, 15.0, 16.0, 20.0]
	,?assertEqual(7.0, quantile(1/4, Samples2))
	,?assertEqual(9.0, quantile(1/2, Samples2))
	,?assertEqual(15.0, quantile(3/4, Samples2))
	,?assertEqual(1.0, quantile(1/4, [1.0]))
	,?assertEqual(1.0, quantile(2/4, [1.0]))
	,?assertEqual(1.0, quantile(3/4, [1.0])).

-endif.
