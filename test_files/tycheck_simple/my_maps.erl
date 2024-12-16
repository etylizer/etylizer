-module(maps).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%% Currently (2024-09-16), we only support maps as dictionaries. So we comment out
%% tests for maps with more than one key-value type.

%%%%%%%%%%%%%%%%%%%%%%%% CONSTRUCTION %%%%%%%%%%%%%%%%%%%%%%%

-spec const_map_00() -> map().
const_map_00() -> #{ a => 1, b => 2 }.

-spec const_map_00_fail() -> map().
const_map_00_fail() -> 1.

-spec empty_map() -> #{}.
empty_map() -> #{}.

%% DISABLED because we only support maps as dictionaries
%% -spec const_map_01() -> #{ a := 1, b := 2}.
%% const_map_01() -> #{ a => 1, b => 2 }.
%%
%% -spec const_map_02() -> #{ a := integer(), b := 2}.
%% const_map_02() -> #{ a => 1, b => 2 }.
%%
%% -spec const_map_03() -> #{ a := integer(), b => 2}.
%% const_map_03() -> #{ a => 1, b => 2 }.
%%
%% -spec const_map_04() -> #{ a := integer(), b => 2}.
%% const_map_04() -> #{ a => 1 }.
%%
%% -spec const_map_05_fail() -> #{ a := integer(), b := 2}.
%% const_map_05_fail() -> #{ a => 1 }. % b is mandatory
%%
%% -spec const_map_06_fail() -> #{ a := integer(), b := 2}.
%% const_map_06_fail() -> #{ a => 1, b => 3 }. % b with wrong type
%%
%% -spec const_map_07() -> #{ a := integer(), b := 3, b := 2}. % left-most has precedence
%% const_map_07() -> #{ a => 1, b => 3 }.

-spec const_map_08() -> #{ atom() => 1 | 2 }.
const_map_08() -> #{ a => 1, b => 2 }.

-spec const_map_09() -> #{ atom() => 1 | 2 }.
const_map_09() -> #{ a => 1, b => 2, c => 2 }.

-spec const_map_10_fail() -> #{ atom() => 1 | 2 }.
const_map_10_fail() -> #{ a => 1, b => 2, c => 3 }. % c with wrong type

-spec const_map_11_fail() -> #{ atom() => 1 | 2 }.
const_map_11_fail() -> #{ a => 1, "b" => 2 }. % key "b" with wrong type

-spec const_map_12() -> #{ atom() => integer() }.
const_map_12() -> #{ a => 1, b => 2, c => 42 }.

-spec const_map_13_fail() -> #{ atom() => integer() }.
const_map_13_fail() -> #{ "a" => 1, b => 2, c => 42 }. % key "a" with wrong type

-spec const_map_14_fail() -> #{ atom() => integer() }.
const_map_14_fail() -> #{ a => 1, b => 2, c => "42" }. % value of c has wrong type

-spec const_map_15() -> #{ atom() => integer() }.
const_map_15() -> #{  }.

%% DISABLED because we only support maps as dictionaries
%% -spec const_map_16() -> #{ atom() := integer() }. % map type is nonsense
%% const_map_16() -> #{ a => 1, b => 2, c => 42 }.

-spec const_map_17() -> #{ {integer(), string()} => atom() }.
const_map_17() -> #{ {42, "foo"} => a, {1, "bar"} => b}.

-spec const_map_18_fail() -> #{ {integer(), string()} => atom() }.
const_map_18_fail() -> #{ {42, 0} => a, {1, "bar"} => b}. % first key has wrong type

-spec const_map_19_fail() -> #{ {integer(), string()} => atom() }.
const_map_19_fail() -> #{ {42, "foo"} => a, {1, "bar"} => "no"}. % second value has wrong type

%% DISABLED because we only support maps as dictionaries
%% -spec const_map_20() -> #{ a := integer(), atom() => integer() }.
%% const_map_20() -> #{a => 20}.
%%
%% -spec const_map_21() -> #{ a := integer(), atom() => integer() }.
%% const_map_21() -> #{a => 20, b => 21}.
%%
%% -spec const_map_22_fail() -> #{ a := integer(), atom() => integer() }.
%% const_map_22_fail() -> #{b => 21}. % a not present, fails
%%
%% -spec const_map_23() -> #{ a := integer(), atom() => any() }.
%% const_map_23() -> #{a => 20, b => "21"}.
%%
%% -spec const_map_24_fail() -> #{ a := integer(), atom() => any() }.
%% const_map_24_fail() -> #{a => "20", b => "21"}. % a of wrong type, fails

-spec const_map_25() -> any().
const_map_25() -> #{ a => 1, b => 2 }.

-spec const_map_26_fail() -> atom().
const_map_26_fail() -> #{ a => 1, b => 2 }.

%%%%%%%%%%%%%%%%%%%%%%%% INSERT/UPDATE %%%%%%%%%%%%%%%%%%%%%%%

-spec insert_01(#{ atom() => integer() }) -> #{ atom() => integer() }.
insert_01(M) -> M # { a => 42}.

-spec insert_02(#{ atom() => integer() }) -> #{ atom() => integer() }.
insert_02(M) -> M # { a := 42}.

-spec insert_03(atom(), integer(), #{ atom() => integer() }) -> #{ atom() => integer() }.
insert_03(K, V, M) -> M # { K => V}.

-spec insert_04(atom(), integer(), #{ atom() => integer() }) -> #{ atom() => integer() }.
insert_04(K, V, M) -> M # { K := V }.

-spec insert_05_fail(#{ atom() => integer() }) -> #{ atom() => integer() }.
insert_05_fail(M) -> M # { "foo" => 42}. % key has wrong type

-spec insert_06_fail(#{ atom() => integer() }) -> #{ atom() => integer() }.
insert_06_fail(M) -> M # { a => "42"}. % value has wrong type

%%%%%%%%%%%%%%%%%%%%%%%% PATTERN MATCHING %%%%%%%%%%%%%%%%%%%%%%%

-spec match_01(#{ atom() => integer() }) -> integer().
match_01(M) ->
    case M of
        #{a := I} -> I;
        #{b := I} -> I + 1;
        _ -> 0
    end.

-spec match_02_fail(#{ atom() => integer() }) -> integer().
match_02_fail(M) ->
    case M of
        #{a := I} -> I % incomplete pattern
    end.

-spec match_empty(#{ atom() => integer() }) -> 1.
match_empty(M) ->
    case M of
        #{} -> 1
    end.

-spec match_empty_fail(#{ atom() => integer() }) -> integer().
match_empty_fail(M) ->
    case M of
        #{} -> 1;
        _ -> 2  % redundant
    end.

% map types with mandatory associations are not supported
%% -spec match_03(#{ a := integer() }) -> integer().
%% match_03(M) ->
%%     case M of
%%         #{a := I} -> I % complete pattern because key a is mandatory
%%     end.

-spec match_04(#{ atom() => integer() }) -> integer().
match_04(M) ->
    case M of
        #{a := I, b := J } -> I + J;
        _ -> 0
    end.

-spec match_05(#{ atom() => integer() }) -> integer().
match_05(M) ->
    case M of
        #{a := I, a := J } -> I + J;
        _ -> 0
    end.

-spec match_06(atom(), #{ atom() => integer() }) -> integer().
match_06(X, M) ->
    case M of
        #{X := I } -> I;
        _ -> 0
    end.

%% slow, see #144
%% -spec match_07(atom(), #{ {atom(), integer()} => {string(), integer()} }) -> integer().
%% match_07(X, M) ->
%%     case M of
%%         #{{X, 1} := {_, I} } -> I;
%%         #{} -> 0
%%     end.

-spec match_08_fail(atom(), #{ {atom(), integer()} => {string(), integer()} }) -> integer().
match_08_fail(X, M) ->
    case M of
        #{{X, 1} := {_, I} } -> I % incomplete
    end.

%% fails, see #143
%% -spec match_09_fail(integer(), #{ atom() => integer() }) -> integer().
%% match_09_fail(X, M) ->
%%     case M of
%%         #{X := I } -> I; % X has wrong type
%%         _ -> 0
%%     end.

-spec match_10_fail(atom(), #{ atom() => integer() }) -> string().
match_10_fail(X, M) ->
    case M of
        #{X := I } -> I; % I has wrong type
        _ -> "no"
    end.

-spec match_11(atom(), #{ atom() => integer() }) -> integer().
match_11(X, M) ->
    case M of
        #{a := I } -> I;
        #{X := I } -> I;
        _ -> 0
    end.

-spec match_12_fail(#{ atom() => integer() }) -> integer().
match_12_fail(M) ->
    case M of
        #{a := I } -> I;
        #{a := I } -> I; % redundant
        _ -> 0
    end.

-spec match_13(#{ atom() => integer() } | integer()) -> integer().
match_13(M) ->
    case M of
        _ when is_map(M) ->
            case M of
                #{a := I} -> I;
                #{} -> 1
            end;
        _ -> M
    end.

%% slow, see #144
%% -spec match_14(#{ atom() => integer() } | #{ integer() => string() } | integer()) -> integer().
%% match_14(M) ->
%%     case M of
%%         _ when is_map(M) ->
%%             case M of
%%                 #{a := I} -> I;
%%                 #{1 := S} -> length(S);
%%                 #{} -> 1
%%             end;
%%         _ -> M
%%     end.

-spec use_map(#{ atom() => integer() }) -> integer().
use_map(_M) -> 1.

-spec match_15_fail(#{ atom() => integer() } | #{ integer() => string() } | integer()) -> integer().
match_15_fail(M) ->
    case M of
        _ when is_map(M) -> use_map(M); % map has wrong type
        _ -> M
    end.

-spec match_16_fail(#{ atom() => integer() } | integer()) -> integer().
match_16_fail(M) ->
    case M of
        _ when is_map(M) -> M; % wrong type
        _ -> 1
   end.

-spec match_17_fail(#{a => integer()} | ok) -> ok.
match_17_fail(#{a := _I}) -> ok;
match_17_fail(V) -> V.
