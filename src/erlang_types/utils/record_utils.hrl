-record(ty, 
  {
    dnf_ty_predefined = dnf_ty_predefined:empty(),
    dnf_ty_atom = dnf_ty_atom:empty(),
    dnf_ty_interval = dnf_ty_interval:empty(),
    dnf_ty_list = dnf_ty_list:empty(),
    dnf_ty_bitstring = dnf_ty_bitstring:empty(),
    ty_tuples = ty_tuples:empty(),
    ty_functions = ty_functions:empty(),
    dnf_ty_map = dnf_ty_map:empty()
  }).

% these helper function assume a fixed order for records in Erlang
% with the first index being the record name

% inefficient (rebuilds record everytime) but dynamic
map(Map, Record) ->
  Fields = record_info(fields, ty),
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
  Fields = record_info(fields, ty),
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
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      Fold(Field, element(Index, Record), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).

binary_fold(BinaryFold, BaseAcc, Record1, Record2) ->
  Fields = record_info(fields, ty),
  lists:foldl(
    fun({Index, Field}, Acc) -> 
      BinaryFold(Field, element(Index, Record1), element(Index, Record2), Acc)
    end, 
    BaseAcc, 
    lists:zip(lists:seq(2, length(Fields) + 1), Fields)
  ).
