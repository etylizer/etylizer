-module(memoize).

%% API
-export([memo_fun/2]).


-spec memo_fun({atom(), term()}, fun(() -> A)) -> A.
memo_fun({Table, Key}, Fun) ->
  case (catch ets:lookup(Table, Key)) of
    [] ->
      Result = Fun(),
      ets:insert_new(Table, [{Key, Result}]),
      Result;
    [{_, Result}] -> Result;

    _ ->
      ets:new(Table, [named_table]),
      memo_fun({Table, Key}, Fun)
  end.
