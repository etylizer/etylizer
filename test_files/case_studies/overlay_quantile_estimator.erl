%% Specs for the functions of the quantile_estimator case study that have none in the source.
-module(overlay_quantile_estimator).
-compile([export_all, nowarn_export_all]).

%% #group{} of quantile_estimator.hrl: a record of another module has no name here
-type group() :: {group, V :: number(), G :: number(), Delta :: number(), Rank :: number()}.

%% --- quantile ---

%% the rank, or the mean of the two ranks that ranks/2 gives
-spec 'quantile:rank_average'(Size :: integer(), Quantile :: float()) -> number().
'quantile:rank_average'(_, _) -> error(overlay).

%% --- quantile_estimator ---

%% Walks along the groups, which are ordered by value. Until the sample V has its place it carries
%% the rank of the group before; behind that place V, the invariant (as the atom undefiend) and the
%% rank are undefined, and the ranks of the groups left are raised by one.
-spec 'quantile_estimator:insert'(quantile_estimator:data_sample(), [group()], N :: number(),
                                  quantile_estimator:invariant(), RankLast :: number()) -> [group()]
                               ; (undefined, [group()], N :: number(), undefiend, undefined) -> [group()].
'quantile_estimator:insert'(_, _, _, _, _) -> error(overlay).

%% The groups come in reverse order; Last is the group that the next one can be merged into,
%% undefined at the start and after a merge.
-spec 'quantile_estimator:compress'(quantile_estimator:invariant(), N :: number(), [group()],
                                    Last :: group() | undefined) -> [group()].
'quantile_estimator:compress'(_, _, _, _) -> error(overlay).

-spec 'quantile_estimator:merge'(group(), group()) -> group().
'quantile_estimator:merge'(_, _) -> error(overlay).

-spec 'quantile_estimator:quantile'(Phi :: number(), quantile_estimator:invariant(), [group()], N :: number(),
                                    Rank :: number(), Last :: group()) -> number().
'quantile_estimator:quantile'(_, _, _, _, _, _) -> error(overlay).

-spec 'quantile_estimator:floor'(number()) -> integer().
'quantile_estimator:floor'(_) -> error(overlay).

-spec 'quantile_estimator:clamp'(integer()) -> non_neg_integer().
'quantile_estimator:clamp'(_) -> error(overlay).
