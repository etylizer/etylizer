-module(metrics).

-export([
    init/0,
    record/2,
    dump/1,
    cleanup/0,
    current_fun/0,
    inference_fun/1
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
