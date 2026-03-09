-module(records).

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

-spec record_create_03() -> #person{ address :: integer() }.
record_create_03() -> #person{age=13, address=1, name="max"}.

-spec record_create_03_fail() -> #person{ address :: integer() }.
record_create_03_fail() -> #person{name="max", age=13, address="blub"}.

%%%%%%%%%%%%%%%%%%%%%%%% FIELD ACCESS %%%%%%%%%%%%%%%%%%%%%%%

-spec get_name(#person{}) -> string().
get_name(P) -> P#person.name.

-spec get_age(#person{}) -> integer().
get_age(P) -> P#person.age.

-spec get_age_fail(#person{}) -> string().
get_age_fail(P) -> P#person.age.

-spec get_age_02(#person{ age :: string() }) -> string().
get_age_02(P) -> P#person.age.

-spec get_age_02_fail(#person{ age :: string() }) -> integer().
get_age_02_fail(P) -> P#person.age.

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

-spec set_age_02(string()) -> #person{ age :: string() }.
set_age_02(I) -> (record_create_01())#person{age = I}.

-spec set_age_02_fail(#person{ age :: string() }, integer()) -> #person{ age :: string() }.
set_age_02_fail(P, I) -> P#person{age = I}.

-spec set_age_03_fail(#person{ age :: string() }, string()) -> #person{ age :: atom() }.
set_age_03_fail(P, I) -> P#person{age = I}.

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

-spec get_age_02_pattern(#person{ age :: string() }) -> string().
get_age_02_pattern(P) ->
    case P of
        #person{name=_, age=I} -> I
    end.

-spec get_age_02_pattern_fail(#person{ age :: string() }) -> integer().
get_age_02_pattern_fail(P) ->
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

-spec get_name_from_invoice_02(#invoice{ person :: #person { name :: integer() }}) -> integer().
get_name_from_invoice_02(X) -> X#invoice.person#person.name.

-spec get_name_from_invoice_02_fail(#invoice{ person :: #person { name :: integer() }}) -> string().
get_name_from_invoice_02_fail(X) -> X#invoice.person#person.name.

%%%%%%%%%%%%%%%%%%%%%%%% DEFAULT VALUES %%%%%%%%%%%%%%%%%%%%%%%

% Omitting a field with a default value should work
-spec default_01() -> #item{}.
default_01() -> #item{value=1, label="hello"}.

% Providing all fields including the defaulted one should also work
-spec default_02() -> #item{}.
default_02() -> #item{value=1, label="hello", count=5}.

% Omitting a field without a default should fail
-spec default_03_fail() -> #item{}.
default_03_fail() -> #item{value=1}.

%%%%%%%%%%%%%%%%%%%%%%%% WILDCARD FIELD (record_field_other) %%%%%%%%%%%%%%%%%%%%%%%

% Using _ = Expr fills all unspecified fields
-spec wildcard_01() -> #config{}.
wildcard_01() -> #config{host = "localhost", _ = "default"}.

% All fields explicitly given, _ = Expr is a no-op
-spec wildcard_02() -> #config{}.
wildcard_02() -> #config{host = "localhost", port = "80", path = "/", _ = "unused"}.

% _ = Expr with wrong type for the remaining fields should fail
-spec wildcard_03_fail() -> #config{}.
wildcard_03_fail() -> #config{host = "localhost", _ = 42}.

%% recursive

-record(rr, {name :: string(), recursive :: [#rr{}] }).
-spec add1(string(), #rr{}) -> #rr{}.
add1(Name, R) -> #rr{name=Name, recursive=[R]}.

-spec add2(string(), #rr{}) -> #rr{}.
add2(Name, R) -> R#rr{ recursive = [#rr{name=Name, recursive=[]} | R#rr.recursive]}.

-record(rr2, {name :: string(), recursive :: [#rr2{name :: any()}] }).
-spec add3(string(), #rr2{}) -> #rr2{}.
add3(Name, R) -> #rr2{name=Name, recursive=[R]}.

% while the definition is OK, the usage is not and causes a type error
-record(rr3, {name :: string(), recursive :: [#rr3{name :: integer()}] }).
-spec add4_fail(string(), #rr3{}) -> #rr3{}.
add4_fail(Name, R) -> #rr3{name=Name, recursive=[R]}.
