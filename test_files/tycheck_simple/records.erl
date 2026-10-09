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

-spec get_age_03_fail(#person{} | undefined) -> integer().
get_age_03_fail(P) -> P#person.age.

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

-spec set_name_02_fail(#person{} | undefined, string()) -> #person{}.
set_name_02_fail(P, X) -> P#person{name = X}.

% all fields are replaced, the updated value still has to be the record
-spec set_all(#person{}) -> #person{}.
set_all(P) -> P#person{name = "max", age = 13, address = "blub"}.

-spec set_all_fail(#person{} | undefined) -> #person{}.
set_all_fail(P) -> P#person{name = "max", age = 13, address = "blub"}.

% several fields of a record with many fields
-record(wide, {f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12}).

-spec set_wide(#wide{}) -> #wide{}.
set_wide(W) -> W#wide{f1 = 1, f5 = 2, f9 = 3, f12 = 4}.

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

-spec index_pattern_01(2) -> 3.
index_pattern_01(I) ->
    case I of
        #person.name -> #person.age
    end.

-spec index_pattern_02(integer()) -> 2.
index_pattern_02(I) ->
    case I of
        #person.name -> I;
        _ -> 2
    end.

-spec index_pattern_03_fail(integer()) -> 3.
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

%%%%%%%%%%%%%%%%%%%%%%%% GUARDS %%%%%%%%%%%%%%%%%%%%%%%

% a field read in a guard has the type of the field
-spec guard_01(#person{}) -> boolean().
guard_01(P) when P#person.age + 1 > 18 -> true;
guard_01(_) -> false.

-spec guard_02_fail(#person{}) -> boolean().
guard_02_fail(P) when P#person.name + 1 > 18 -> true;
guard_02_fail(_) -> false.

-spec guard_03(#invoice{}) -> boolean().
guard_03(X) when X#invoice.person#person.age > 18 -> true;
guard_03(_) -> false.

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

% A default is evaluated in the scope of the record creation: variables generated for
% the default must not clash with the ones generated there
-record(conv, {f = fun(Y) -> atom_to_list(_ = Y) end :: fun((integer()) -> string())}).

-spec default_04_fail() -> #conv{}.
default_04_fail() -> #conv{}.

-spec default_05_fail(foo) -> #conv{}.
default_05_fail(foo) -> #conv{}.

-spec default_06_fail(foo | bar) -> #conv{} | error.
default_06_fail(Z) ->
    maybe
        foo ?= Z,
        #conv{}
    else
        _ -> error
    end.

% X = Y in the default is a match against an X bound at the record creation
-record(same, {f = fun(Y) -> X = Y, X end :: fun((integer()) -> integer())}).

-spec default_07() -> #same{}.
default_07() -> #same{}.

-spec default_08_fail(integer()) -> {integer(), #same{}}.
default_08_fail(X) -> {X, #same{}}.

% A default is checked against the declared type of its field, also where nothing asks
% for the type of the record
-record(wrong_default, {n = foo :: integer()}).

-spec default_09_fail() -> any().
default_09_fail() -> #wrong_default{}.

-spec default_10() -> #wrong_default{}.
default_10() -> #wrong_default{n = 1}.

% An omitted field has its declared type, not the type of its default
-record(conn, {state = closed :: closed | open}).

-spec default_11() -> ok | error.
default_11() ->
    C = #conn{},
    case C#conn.state of
        closed -> ok;
        open -> error
    end.

-spec default_12_fail() -> ok.
default_12_fail() ->
    C = #conn{},
    case C#conn.state of
        closed -> ok
    end.

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
