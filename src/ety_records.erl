-module(ety_records).

-export([
    encode_record_ty/2,
    encode_record_ty/1,
    record_ty_from_decl/2,
    record_type_name/1,
    reader_name/2,
    readers/1
]).

-export_type([
    record_ty/0,
    record_field/0
]).

-type record_ty() :: {Name::atom(), [record_field()]}.
-type record_field() :: {Name::atom(), Type::ast:ty()}.

-spec record_ty_from_decl(atom(), [ast:record_field()]) -> record_ty().
record_ty_from_decl(RecordName, Fields) ->
    FieldTys =
        lists:map(
            fun ({record_field, _Loc, FieldName, FieldTy, _Default}) ->
                {FieldName,
                case FieldTy of
                    untyped -> stdtypes:tany();
                    T -> T
                end}
            end,
            Fields),
    {RecordName, FieldTys}.

-spec encode_record_ty(record_ty()) -> ast:ty().
encode_record_ty(T) -> encode_record_ty(T, []).

-spec encode_record_ty(record_ty(), [record_field()]) -> ast:ty().
encode_record_ty({Name, Fields}, Overrides) ->
    NameTy = stdtypes:tatom(Name),
    UpdatedFieldTys =
        lists:map(
            fun ({FieldName, FieldTy}) ->
                case utils:assocs_find(FieldName, Overrides) of
                    error -> FieldTy;
                    {ok, T} -> T
                end
            end,
        Fields),
    Tys = [NameTy | UpdatedFieldTys],
    stdtypes:ttuple(Tys).

-spec record_type_name(atom()) -> atom().
record_type_name(RecName) ->
    list_to_atom("$record$" ++ atom_to_list(RecName)).

% '#Rec.Field', the function that reads a field of a record (see readers/1)
-spec reader_name(atom(), atom()) -> atom().
reader_name(RecName, FieldName) ->
    list_to_atom("#" ++ atom_to_list(RecName) ++ "." ++ atom_to_list(FieldName)).

% The reader of every field, with its type. It accepts the record with any values in the
% other fields: '#r.b' :: fun(({r, any(), B, any()}) -> B)
-spec readers(record_ty()) -> [{ast:global_ref(), ast:ty_scheme()}].
readers({RecName, Fields}) ->
    V = '$field',
    lists:map(
      fun({F, _}) ->
              Arg = lists:map(fun({N, _}) when N =:= F -> {N, {var, V}};
                                 ({N, _}) -> {N, stdtypes:tany()}
                              end, Fields),
              {{ref, reader_name(RecName, F), 1},
               {ty_scheme, [{V, stdtypes:tany()}],
                {fun_full, [encode_record_ty({RecName, Arg})], {var, V}}}}
      end, Fields).
