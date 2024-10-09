-module(maps).

-compile(export_all).
-compile(nowarn_export_all).

-include("records.hrl").

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% CONSTRUCTION %%%%%%%%%%%%%%%%%%%%%%%

-spec record_create_01() -> #person{}.
record_create_01() -> #person{age=13, address="blub", name="max"}.

-spec record_create_02_fail() -> #person{}.
record_create_02_fail() -> #person{name="max", age="13", address="blub"}.


%%%%%%%%%%%%%%%%%%%%%%%% FIELD ACCESS %%%%%%%%%%%%%%%%%%%%%%%

-spec get_name(#person{}) -> string().
get_name(P) -> P#person.name.

-spec get_age(#person{}) -> integer().
get_age(P) -> P#person.age.

-spec get_age_fail(#person{}) -> string().
get_age_fail(P) -> P#person.age.

%%%%%%%%%%%%%%%%%%%%%%%% FIELD INDEX %%%%%%%%%%%%%%%%%%%%%%%

-spec age_index() -> integer().
age_index() -> #person.age.

-spec age_index_fail() -> string().
age_index_fail() -> #person.age.

%%%%%%%%%%%%%%%%%%%%%%%% FIELD UPDATE %%%%%%%%%%%%%%%%%%%%%%%

-spec set_name(#person{}, string()) -> #person{}.
set_name(P, X) -> P#person{name = X}.

-spec set_age(integer()) -> #person{}.
set_age(I) -> (record_create_01())#person{age = I}.

-spec set_age_fail(#person{}, string()) -> #person{}.
set_age_fail(P, S) -> P#person{age = S}.

%%%%%%%%%%%%%%%%%%%%%%%% PATTERNS %%%%%%%%%%%%%%%%%%%%%%%

-spec get_name_pattern(#person{}) -> string().
get_name_pattern(P) ->
    case P of
        #person{name=S} -> S
    end.

-spec get_age_pattern(#person{}) -> integer().
get_age_pattern(P) ->
    case P of
        #person{name=_, age=I} -> I
    end.

-spec index_pattern_01(1) -> 2.
index_pattern_01(I) ->
    case I of
        #person.name -> #person.age
    end.

-spec index_pattern_02(integer()) -> 1.
index_pattern_02(I) ->
    case I of
        #person.name -> I;
        _ -> 1
    end.

-spec index_pattern_03_fail(integer()) -> 2.
index_pattern_03_fail(I) ->
    case I of
        #person.name -> #person.age
        % not exhaustive
    end.

%%%%%%%%%%%%%%%%%%%%%%%% NESTED %%%%%%%%%%%%%%%%%%%%%%%

-record(invoice, {person :: #person{}, amount :: float()}).

-spec make_invoice(#person{}) -> #invoice{}.
make_invoice(P) -> #invoice{person = P, amount = 10.1}.

-spec get_age_from_invoice(#invoice{}) -> integer().
get_age_from_invoice(X) ->
    case X of
        #invoice{person=#person{age=I}} -> I
    end.

-spec get_name_from_invoice(#invoice{}) -> string().
get_name_from_invoice(X) -> X#invoice.person#person.name.

