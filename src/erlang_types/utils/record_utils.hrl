-ifndef(RECORD).
-define(RECORD, ty).
-endif.


% these helper function assume a fixed order for records in Erlang
% with the first index being the record name

% inefficient (rebuilds record everytime) but dynamic
map(Map, Record) ->
  Fields = record_info(fields, ?RECORD),
  lists:foldl(
    fun({Index, Field}, Rec) -> 
      OldValue = element(Index, Record),
      setelement(Index, Rec, Map(Field, OldValue))
    end, 
    Record, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

% same as map, but mapping over two records at once
binary_map(BinaryMap, Record1, Record2) ->
  Fields = record_info(fields, ?RECORD),
  lists:foldl(
    fun({Index, Field}, Rec) -> 
      OldLeftValue = element(Index, Record1),
      OldRightValue = element(Index, Record2),
      setelement(Index, Rec, BinaryMap(Field, OldLeftValue, OldRightValue))
    end, 
    Record1, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

fold(Fold, BaseAcc, Record) ->
  Fields = record_info(fields, ?RECORD),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      Fold(Field, element(Index, Record), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

binary_fold(BinaryFold, BaseAcc, Record1, Record2) ->
  Fields = record_info(fields, ?RECORD),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      BinaryFold(Field, element(Index, Record1), element(Index, Record2), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).