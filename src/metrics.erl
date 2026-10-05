-module(metrics).

-export([
    init/0,
    record/2,
    dump/1,
    cleanup/0,
    current_fun/0,
    inference_fun/1,
    begin_invocation/0,
    set_stage/1,
    count/2,
    flush_counts/0,
    record_partition_vars/2
]).

-define(TABLE, ety_metrics_table).

-spec init() -> ok.
init() ->
    ets:new(?TABLE, [named_table, duplicate_bag, public]),
    ok.

% Label of the function being checked, or '__no_fun__' outside one.
-spec current_fun() -> atom().
current_fun() ->
    case erlang:get(ety_cur_fun) of
        undefined -> '__no_fun__';
        Label -> Label
    end.

% Shaped like a function label so it cannot collide with a real one.
-spec inference_fun(file:filename()) -> atom().
inference_fun(FileName) ->
    list_to_atom(utils:sformat("~s:__inference__/0",
                               [filename:basename(filename:rootname(FileName))])).

-spec record(atom(), term()) -> ok.
record(Category, DataPoint) ->
    try
        ets:insert(?TABLE, {Category, DataPoint}),
        ok
    catch
        error:badarg -> ok
    end.

% Counts are kept in the process dictionary of the checking process: the
% counting sites (deep in erlang_types) are hot and know neither the function
% nor the tally invocation. tally.erl sets the stage of the invocation (pre:
% the rewrites before tally, tally: tally itself) and flushes the counts at its
% end; outside an invocation nothing is counted.
%
% A decomposition takes a structure apart. Via says where: rule for the
% rewrites before tally (kind: the rule), norm for the subproblems of
% normalize, subty for those of the emptiness check. Their kind is the search:
% tuple for dnf_ty_tuple:phi_norm and phi, which also take lists and maps
% apart, function for dnf_ty_function:explore_function_norm and phi. Cached
% results are not counted, only work done.
-define(COUNT_KEY(Stage, Via, Kind), {ety_metrics_count, Stage, Via, Kind}).

% Starts a tally invocation: drops what a killed earlier one left behind.
-spec begin_invocation() -> ok.
begin_invocation() ->
    _ = [erlang:erase(K) || {K = ?COUNT_KEY(_, _, _), _} <- erlang:get()],
    set_stage(pre).

-spec set_stage(pre | tally) -> ok.
set_stage(Stage) ->
    erlang:put(ety_metrics_stage, Stage),
    ok.

-spec count(atom(), atom()) -> ok.
count(Via, Kind) ->
    case erlang:get(ety_metrics_stage) of
        undefined -> ok;
        Stage ->
            Key = ?COUNT_KEY(Stage, Via, Kind),
            case erlang:get(Key) of
                undefined -> erlang:put(Key, 1);
                N -> erlang:put(Key, N + 1)
            end,
            ok
    end.

% Records one `decompositions` row {Fun, Stage, Via, Kind, Count} per counter,
% resets all counters and ends the invocation.
-spec flush_counts() -> ok.
flush_counts() ->
    Fun = current_fun(),
    erlang:erase(ety_metrics_stage),
    lists:foreach(
        fun({Key = ?COUNT_KEY(Stage, Via, Kind), N}) ->
                erlang:erase(Key),
                record(decompositions, {Fun, Stage, Via, Kind, N});
           (_) -> ok
        end, lists:sort(erlang:get())).

% A partition variable holds its tally partition together: without it (fixed,
% so that it links no constraints) tally:split/2 cuts the partition into more
% than one. Recorded per partition as {Fun, NumVars, NumPartitionVars}, where
% NumVars counts every variable split/2 links by, frame variables included.
%
% The bottleneck variables of a tally invocation are the partition variables of
% its biggest partition (most constraints; the first one on a tie), the one that
% usually costs most. Recorded per invocation with partitions as
% {Fun, NumConstraints, NumVars, NumBottleneckVars}.
-spec record_partition_vars([[{ast:ty(), ast:ty()}]], sets:set(ast:ty_varname())) -> ok.
record_partition_vars([], _Fixed) -> ok;
record_partition_vars(Partitions, Fixed) ->
    Fun = current_fun(),
    Counts = lists:map(
        fun(P) ->
            VarSets = [free_vars(C, Fixed) || C <- P],
            Vars = lists:usort(lists:append(VarSets)),
            PartitionVars = [V || V <- Vars, components([Vs -- [V] || Vs <- VarSets]) > 1],
            record(tally_partition_vars, {Fun, length(Vars), length(PartitionVars)}),
            {length(P), length(Vars), length(PartitionVars)}
        end, Partitions),
    Biggest = lists:foldl(
        fun(C = {N, _, _}, {Max, _, _}) when N > Max -> C;
           (_, Acc) -> Acc
        end, hd(Counts), tl(Counts)),
    record(tally_bottleneck_vars, erlang:insert_element(1, Biggest, Fun)).

-spec free_vars({ast:ty(), ast:ty()}, sets:set(ast:ty_varname())) -> [ast:ty_varname()].
free_vars(Constraint, Fixed) ->
    lists:usort(utils:everything(
        fun({var, V}) when is_atom(V) ->
                case sets:is_element(V, Fixed) of true -> error; false -> {ok, V} end;
           (_) -> error
        end, Constraint)).

% The number of groups tally:split/2 makes of constraints with these variables:
% constraints sharing a variable are in one group, a ground one is its own.
components(VarSets) ->
    {Groups, Ground} = lists:foldl(
        fun([], {Gs, N}) -> {Gs, N + 1};
           (Vs, {Gs, N}) ->
                S = sets:from_list(Vs),
                {Touching, Rest} = lists:partition(fun(G) -> not sets:is_disjoint(G, S) end, Gs),
                {[sets:union([S | Touching]) | Rest], N}
        end, {[], 0}, VarSets),
    length(Groups) + Ground.

-spec dump(file:filename()) -> ok.
dump(Path) ->
    Entries = ets:tab2list(?TABLE),
    Grouped = lists:foldl(
        fun({Category, DataPoint}, Acc) ->
            maps:update_with(Category, fun(Old) -> [DataPoint | Old] end, [DataPoint], Acc)
        end,
        #{},
        Entries
    ),
    JsonMap = maps:fold(
        fun(Category, DataPoints, Acc) ->
            Acc#{atom_to_binary(Category, utf8) => lists:reverse([tuple_to_list(DP) || DP <- DataPoints])}
        end,
        #{},
        Grouped
    ),
    JsonBin = json:encode(JsonMap),
    ok = file:write_file(Path, JsonBin).

-spec cleanup() -> ok.
cleanup() ->
    try
        ets:delete(?TABLE),
        ok
    catch
        error:badarg -> ok
    end.
