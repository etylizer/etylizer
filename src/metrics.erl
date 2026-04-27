-module(metrics).

-export([
    init/0,
    record/2,
    dump/1,
    cleanup/0
]).

-define(TABLE, ety_metrics_table).

-spec init() -> ok.
init() ->
    ets:new(?TABLE, [named_table, bag, public]),
    ok.

-spec record(atom(), term()) -> ok.
record(Category, DataPoint) ->
    try
        ets:insert(?TABLE, {Category, DataPoint}),
        ok
    catch
        error:badarg -> ok
    end.

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
