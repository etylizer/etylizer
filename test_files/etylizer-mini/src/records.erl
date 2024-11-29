-module(records).

-export([
    encode_record_ty/2,
    encode_record_ty/1,
    record_ty_from_decl/2,
    lookup_field_ty/3,
    lookup_field_index/3
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

-spec lookup_field_ty(record_ty(), atom(), ast:loc()) -> ast:ty().
lookup_field_ty(RecTy, FieldName, L) ->
    {T, _} = lookup_field_index(RecTy, FieldName, L),
    T.

-spec lookup_field_index(record_ty(), atom(), ast:loc()) -> {ast:ty(), integer()}.
lookup_field_index({RecName, DefFields}, FieldName, L) ->
    case utils:assocs_find_index(FieldName, DefFields) of
        error ->
            errors:ty_error(L, "Field ~w not defined for record ~w", [FieldName, RecName]);
        {ok, untyped, _} ->
            errors:ty_error(L, "No type for field ~w of record ~w", [FieldName, RecName]);
        {ok, FieldTy, I} ->
            {FieldTy, I}
    end.
