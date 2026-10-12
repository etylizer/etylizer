-module(quantile_estimator).
-author('Florian Odronitz <odo@mac.com>').

% Based on:
% Cormode et. al.:
% "Effective Computation of Biased Quantiles over Data Streams"

-export([
	new/1,
	insert/2,
	quantile/2,
	compress/1,
	inserts_since_compression/1
]).

-export([
	f_biased/1,
	f_targeted/1
]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-define(DEBUG, true).
-endif.

-include("quantile_estimator.hrl").

-type data_sample() :: number().
-type invariant() :: fun((number(), number()) -> number()).
	
-spec f_biased(number()) -> invariant().
f_biased(Epsilon) ->
	fun(Rank, _N) ->
		2 * Epsilon * Rank
	end.

-spec f_targeted([{number(), number()}]) -> invariant().
f_targeted(Targets) ->
	TargetFuns = [f_targeted(Phi, Epsilon)||{Phi, Epsilon} <- Targets],
	fun(Rank, N) ->
		lists:min([TargetFun(Rank, N)||TargetFun<-TargetFuns])
	end.

-spec f_targeted(number(), number()) -> invariant().
f_targeted(Phi, Epsilon) ->
	fun(Rank, N) ->
		case Phi * N =< Rank of
			true ->
				(2 * Epsilon * Rank) / Phi;
			false ->
				(2 * Epsilon * (N - Rank)) / (1 - Phi)
		end
	end.

-spec new(invariant()) -> #quantile_estimator{}.
new(Invariant) ->
	#quantile_estimator{samples_count = 0, inserts_since_compression = 0, data_count = 0, data = [], invariant = Invariant}.

-spec inserts_since_compression(#quantile_estimator{}) -> non_neg_integer().
inserts_since_compression(#quantile_estimator{inserts_since_compression = InsertsSinceCompression}) ->
	InsertsSinceCompression.

-spec insert(data_sample(), #quantile_estimator{}) -> #quantile_estimator{}.
insert(V, QE = #quantile_estimator{samples_count = SamplesCount, inserts_since_compression = InsertsSinceCompression, data_count = DataCount, data = Data, invariant = Invariant}) ->
	QE#quantile_estimator{
		samples_count = SamplesCount + 1,
		inserts_since_compression = InsertsSinceCompression + 1,
		data_count = DataCount + 1,
		data = insert(V, Data, SamplesCount, Invariant, 0)
	}.

% we terminate and the group has been added
insert(undefined, [], _N, _Invariant, _Rank) ->
	[];

% we terminate but the group has not been added yet
% so this is the maximum value
insert(V, [], _, _, RankLast) ->
	[#group{v = V, g = 1, delta = 0, rank = RankLast + 1}];

% the group has already been inserted, just append
% and increase the rank by 1
insert(undefined, [Next = #group{rank = RankNext}|DataTail], N, _, undefined) ->
	NextUpdated = Next#group{rank = RankNext + 1},
	[NextUpdated|insert(undefined, DataTail, N, undefiend, undefined)];

% the group has not yet been insterted
% insert it and continue
insert(V, [Next = #group{v = Vi, g = Gi, rank = RankNext}|DataTail], N, Invariant, RankLast) ->
	Ranki = RankLast + Gi,
	% did we pass a smaller Vi?
	case Vi >= V of
		true ->
			GroupNew = 
			case Ranki =:= 1 of
				true  -> #group{v = V, g = 1, delta = 0, rank = RankLast + 1};
				false -> #group{v = V, g = 1, delta = clamp(floor(Invariant(Ranki, N)) - 1), rank = RankLast +1}
			end,
			[GroupNew|[Next#group{rank = RankNext + 1}|insert(undefined, DataTail, N, undefiend, undefined)]];
		false ->
			[Next|insert(V, DataTail, N, Invariant, Ranki)]
	end.

-spec compress(#quantile_estimator{}) -> #quantile_estimator{}.
compress(QE = #quantile_estimator{samples_count = N, data = Data, invariant = Invariant}) ->
	DataCompressed = lists:reverse(compress(Invariant, N, lists:reverse(Data), undefined)),
	QE#quantile_estimator{
		samples_count = N,
		inserts_since_compression = 0,
		data_count = length(DataCompressed),
		data = DataCompressed
	}.

% This is the first call that just splits off one group as a merge candidate
compress(Invariant, N, [Next | Rest], undefined)->
	compress(Invariant, N, Rest, Next);

% only one group is left
compress(_, _, [], Last) ->
	[Last];

% we never merge the two last groups since the edge groups need to be untouched
compress(_, _, [Next], Last) ->
	[Last|[Next]];

compress(Invariant, N, [Next = #group{g = Gi, rank = Ranki} | Rest], Last = #group{g = Giplusone, delta = Deltaiplusone}) ->
	% 		error_logger:info_msg("Rank:~p\n", [Ranki]),
	% error_logger:info_msg("comress ~p =< ~p \n", [(Gi + Giplusone + Deltaiplusone), Invariant(Ranki, N)]),
	% 		error_logger:info_msg("Last:~p\n", [Last]),
	case Gi + Giplusone + Deltaiplusone =< Invariant(Ranki, N) of
		true ->
			% [Last|[Next|compress(Invariant, N, Rest, Ranki + Gi, undefined)]];
			[merge(Last, Next)|compress(Invariant, N, Rest, undefined)];
		false ->
			[Last|compress(Invariant, N, Rest, Next)]
	end.

merge(#group{g = Giplusone, v = Viplusone, delta = Deltaiplusone, rank = Rankiplusone}, #group{g = Gi, rank = Ranki}) ->
	C = Rankiplusone > Ranki,
	% error_logger:info_msg("{Rankiplusone, Ranki, C}: ~p\n", [{Rankiplusone, Ranki, C}]),
	C = true,
	% error_logger:info_msg("merging...GI:~p , Giplusone:~p\n", [Gi, Giplusone]),
	#group{v = Viplusone, g = Gi + Giplusone, delta = Deltaiplusone, rank = Ranki}.

-spec quantile(number(), #quantile_estimator{}) -> number().
quantile(_, #quantile_estimator{data = []}) ->
	throw({error, empty_stats});

quantile(Phi, #quantile_estimator{samples_count = N, data = [First|DataStructure], invariant = Invariant}) ->
	quantile(Phi, Invariant, DataStructure, N, 0, First).

quantile(_, _, [], _, _, #group{v = Vlast}) ->
	Vlast;

quantile(Phi, Invariant, [Next = #group{g = Gi, delta = Deltai}|DataStructure], N, Rank, #group{v = Vlast}) ->
	case (Rank + Gi + Deltai) > (Phi * N + Invariant(Phi * N, N) / 2) of
		true ->
			Vlast;
		false ->
			quantile(Phi, Invariant, DataStructure, N, Rank + Gi, Next)
	end.

floor(X) ->
    T = erlang:trunc(X),
    case (X - T) of
        Neg when Neg < 0 -> T - 1;
        Pos when Pos > 0 -> T;
        _ -> T
    end.

clamp(X) when X >= 0 -> X;
clamp(X) when X < 0 -> 0.


-ifdef(TEST).

quantile_estimator_test_() ->
[{foreach, local,
	fun test_setup/0,
	fun test_teardown/1,
	[
		{"simple insert", fun test_insert/0}
		,{"quantiles are working", fun test_quantile/0}
		,{"quantiles are working with compression and biased quantiles", fun test_compression_biased/0}
		,{"quantiles are working with compression and targeted quantiles", fun test_comression_targeted/0}
		% ,{"quantiles are working with long tail data set", timeout, 1000, fun test_long_tail/0}
	]}
].

test_setup() -> nothing.
test_teardown(_) -> nothing.

qe(SamplesCount, Data, Invariant) ->
	qe(SamplesCount, SamplesCount, Data, Invariant).

qe(SamplesCount, InsertsSinceCompression, Data, Invariant) ->
	#quantile_estimator{
		samples_count = SamplesCount,
		inserts_since_compression = InsertsSinceCompression,
		data_count = length(Data),
		data = Data,
		invariant = Invariant
	}.

test_insert() ->
	Invariant = f_biased(0.001),
	QE1 = insert(13, quantile_estimator:new(Invariant)),
	?assertEqual(
		qe(1, [#group{v = 13, g = 1, delta = 0, rank = 1}], Invariant),
	QE1),
	QE2 = insert(2, QE1),
	?assertEqual(
		qe(2,
			[
			#group{v = 2,  g = 1, delta = 0, rank = 1},
			#group{v = 13, g = 1, delta = 0, rank = 2}
			]
			, Invariant
		),
	QE2),
	QE3 = insert(8, QE2),
	?assertEqual(
		qe(3,
			[
			#group{v = 2,  g = 1, delta = 0, rank = 1},
			#group{v = 8,  g = 1, delta = 0, rank = 2},
			#group{v = 13, g = 1, delta = 0, rank = 3}
			]
			, Invariant
		),
	QE3),
	QE4 = insert(-3, QE3),
	?assertEqual(
		qe(4,
			[
			#group{v = -3, g = 1, delta = 0, rank = 1},
			#group{v = 2,  g = 1, delta = 0, rank = 2},
			#group{v = 8,  g = 1, delta = 0, rank = 3},
			#group{v = 13, g = 1, delta = 0, rank = 4}
			]
			, Invariant
		),
	QE4),
	QE5 = insert(99, QE4),
	?assertEqual(
		qe(5,
			[
			#group{v = -3, g = 1, delta = 0, rank = 1},
			#group{v = 2,  g = 1, delta = 0, rank = 2},
			#group{v = 8,  g = 1, delta = 0, rank = 3},
			#group{v = 13, g = 1, delta = 0, rank = 4},
			#group{v = 99, g = 1, delta = 0, rank = 5}
			]
			, Invariant
		),
	QE5),
	QE6 = insert(14, QE5),
	?assertEqual(
		qe(6,
			[
			#group{v = -3, g = 1, delta = 0, rank = 1},
			#group{v = 2,  g = 1, delta = 0, rank = 2},
			#group{v = 8,  g = 1, delta = 0, rank = 3},
			#group{v = 13, g = 1, delta = 0, rank = 4},
			#group{v = 14, g = 1, delta = 0, rank = 5},
			#group{v = 99, g = 1, delta = 0, rank = 6}
			]
			, Invariant
		),
	QE6).

test_quantile() ->
	% we create a set of 1000 random values and test if the guarantees are met
	Invariant = f_biased(0.001),
	N = 1000,
	Samples = [random:uniform()||_ <- lists:seq(1, N)],
	Data = lists:foldl(fun(Sample, Stats) -> insert(Sample, Stats) end, quantile_estimator:new(Invariant), Samples),
	% error_logger:info_msg("D:~p\n", [D]),
	validate(Samples, Invariant, Data),
	Samples2 = [5],
	Data2 = lists:foldl(fun(Sample, Stats) -> insert(Sample, Stats) end, quantile_estimator:new(Invariant), Samples2),
	?assertEqual(5, quantile(0, Data2)),
	?assertEqual(5, quantile(1, Data2)),
	?assertEqual(5, quantile(0.99, Data2)).

	
test_compression_biased() ->
	% we create a set of 1000 random values and test if the guarantees are met
	Invariant = f_biased(0.01),
	N = 2000,
	Samples = [random:uniform()||_ <- lists:seq(1, N)],
	Data = lists:foldl(fun(Sample, Stats) -> insert(Sample, Stats) end, quantile_estimator:new(Invariant), Samples),
	DL = Data#quantile_estimator.data,
	validate(Samples, Invariant, Data),
	compress_and_validate(Samples, Invariant, Data, length(DL)).

test_comression_targeted() ->
	% we create a set of 1000 random values and test if the guarantees are met
	Invariant = quantile_estimator:f_targeted([{0.05, 0.005}, {0.5, 0.02}, {0.95, 0.005}]),
	N = 2000,
	Samples = [random:uniform()||_ <- lists:seq(1, N)],
	Data = lists:foldl(fun(Sample, Stats) -> insert(Sample, Stats) end, quantile_estimator:new(Invariant), Samples),
	DL = Data#quantile_estimator.data,
	validate(Samples, Invariant, Data),
	compress_and_validate(Samples, Invariant, Data, length(DL)).

test_long_tail() ->
	{ok, [Samples]} = file:consult(os:getenv("TESTDIR") ++ "us_city_populations"),
	Invariant = quantile_estimator:f_targeted([{0.01, 0.005}, {0.05, 0.005}, {0.5, 0.025}, {0.95, 0.005}, {0.99, 0.005}]),
	% Invariant = quantile_estimator:f_biased(0.001),
	lists:foldl(
		fun(Sample, {Stats = #quantile_estimator{data = DL}, SamplesUsed}) ->
			% error_logger:info_msg("Stats:~p\n", [Stats]),
			StatsNew = insert(Sample, Stats),
			SamplesNew = [Sample|SamplesUsed],
			% error_logger:info_msg("StatsNew:~p\n", [StatsNew]),
			validate(SamplesNew, Invariant, StatsNew),
			StatsCompressed =
			case length(SamplesUsed) rem 10 =:= 0 of
				true ->
					compress_and_validate(SamplesNew, Invariant, StatsNew, length(DL));
					% StatsNew;
				false ->
					StatsNew
			end,
			{StatsCompressed, SamplesNew}
		end,
		{quantile_estimator:new(Invariant), []},
		Samples
	).

validate(Samples, Invariant, Estimate = #quantile_estimator{samples_count = N, data = Series}) ->
	Index = fun(Element, List) -> length(lists:takewhile(fun(E) -> E < Element end, List)) end,
	SamplesSort = lists:sort(Samples),
	validate_ranks(Series, 0),
	Quantiles = [0.01, 0.05, 0.10, 0.5, 0.90, 0.95, 0.99],
	RankestRankrealDevDevallowed = [
		{
			Index(quantile:quantile(Q, SamplesSort), SamplesSort), 
			Index(quantile(Q, Estimate), SamplesSort), 
			abs(Index(quantile:quantile(Q, SamplesSort), SamplesSort) - Index(quantile(Q, Estimate), SamplesSort)),
			quantile:ceil(Invariant(Index(quantile(Q, Estimate), SamplesSort), N))
		} || Q <- Quantiles],
	% [error_logger:info_msg("QReal:~p,~p,~p\n", [Q, N, quantile:quantile(Q, SamplesSort)]) || Q <- [0.0, 1.0]],
	% [error_logger:info_msg("QEst:~p,~p,~p\n", [Q, N, quantile(Q, Invariant, Estimate)]) || Q <- [0.0, 1.0]],
	% [error_logger:info_msg("QReal:~p,~p,~p\n", [Q, N, quantile:quantile(Q, SamplesSort)]) || Q <- Quantiles],
	% [error_logger:info_msg("QEst:~p,~p,~p\n", [Q, N, quantile(Q, Invariant, Estimate)]) || Q <- Quantiles],
	% error_logger:info_msg("N:~p, RankestRankrealDevDevallowed:~p\n", [N, RankestRankrealDevDevallowed]),
	[?assertEqual(true, (Dev =< DevAlloweddev)) || {_, _, Dev, DevAlloweddev} <- RankestRankrealDevDevallowed].
			
validate_ranks([_], _) ->
	undefined;

validate_ranks([#group{rank = Rank}|Rest], RankLast)	->
	?assert(Rank > RankLast),
	validate_ranks(Rest, Rank).
% validate(Samples, Invariant, Data = {N, _}) ->
% 	SamplesSort = lists:sort(Samples),
% 	RankEstimate = [{R, quantile((R-1)/N, Invariant, Data)}||R<-[1, N*0.01, N*0.05, N*0.10, N*0.5, N*0.90, N*0.95, N*0.99, N]],
% 	RankEstimateRank = [{Rank, string:str(SamplesSort, [Estimate])}||{Rank, Estimate} <- RankEstimate],
% 	error_logger:info_msg("N:~p\n", [N]),
% 	error_logger:info_msg("RankEstimateRank:~p\n", [RankEstimateRank]),
% 	DeviationAllowedDeviation = [{abs(Rank - EstimateRank), Invariant(Rank, N)} || {Rank, EstimateRank} <- RankEstimateRank],
% 	error_logger:info_msg("DeviationAllowedDeviation:~p\n", [DeviationAllowedDeviation]),
% 	[?assert(Deviation =< AllowedDeviation)||{Deviation, AllowedDeviation} <- DeviationAllowedDeviation].

compress_and_validate(Samples, Invariant, Est, SizeLast) ->
	% error_logger:info_msg("before compress {N, Data}: ~p\n", [Data]),
	EstCompressed = compress(Est),
	% error_logger:info_msg("DataCompressed: ~p\n", [DataCompressed]),
	?assertEqual(Est#quantile_estimator.samples_count, EstCompressed#quantile_estimator.samples_count),
	?assertEqual(0, EstCompressed#quantile_estimator.inserts_since_compression),
	% error_logger:info_msg("------->reduced from :~p to: ~p\n", [length(List), length(ListCompressed)]),
	% error_logger:info_msg("ratio: ~p,~p\n", [N, length(ListCompressed)]),
	?assert(length(EstCompressed#quantile_estimator.data) =< length(Est#quantile_estimator.data)),
	?assertEqual(length(EstCompressed#quantile_estimator.data), EstCompressed#quantile_estimator.data_count),
	% error_logger:info_msg("DataCompressed:~p\n", [DataCompressed]),
	validate(Samples, Invariant, EstCompressed),
	case length(EstCompressed#quantile_estimator.data) < SizeLast of
		true ->
			compress_and_validate(Samples, Invariant, EstCompressed, length(EstCompressed#quantile_estimator.data));
		false ->
			EstCompressed
	end.

-endif.

