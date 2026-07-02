-module(maybe_expr).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail

%%%%%%%%%%%%%%%%%%%%%%%% IF %%%%%%%%%%%%%%%%%%%%%%%

-spec maybe_01() -> ok.
maybe_01() ->
    maybe ok end.

-spec maybe_02() -> ok.
maybe_02() ->
    maybe nok, ok end.

-spec maybe_03() -> ok.
maybe_03() ->
    maybe nok, begin okk, ok end end.

-spec maybe_04_fail() -> ok.
maybe_04_fail() ->
    maybe ok, nok end.

-spec maybe_match_01() -> ok.
maybe_match_01() ->
    maybe nok ?= ok end.

-spec maybe_match_02() -> ok.
maybe_match_02() ->
    maybe ok ?= ok end.

% maybe_match never matches
-spec maybe_match_03_fail() -> ok.
maybe_match_03_fail() ->
    maybe nok ?= ok, bad end.

-spec maybe_match_04(some | error) -> ok | error.
maybe_match_04(Arg) ->
    maybe some ?= Arg, ok end.

-spec maybe_match_05_fail(some | err) -> ok | error.
maybe_match_05_fail(Arg) ->
    maybe some ?= Arg, ok end.

-spec maybe_match_06(some | error, some2 | error) -> ok | error.
maybe_match_06(Arg, Arg2) ->
    maybe 
        some ?= Arg, 
        some2 ?= Arg2, 
        ok 
    end.

-spec maybe_match_07(some | error, some2 | error, some3 | error) -> ok | error.
maybe_match_07(Arg, Arg2, Arg3) ->
    maybe 
        some ?= maybe
                    some ?= Arg,
                    some3 ?= Arg3,
                    some
                end, 
        some2 ?= Arg2, 
        ok 
    end.

-spec maybe_else_01_fail() -> ok.
maybe_else_01_fail() ->
    maybe ok else _ -> error(badarg) end.

-spec maybe_else_02_fail() -> ok.
maybe_else_02_fail() ->
    maybe ok ?= bad else _ -> error(badarg) end.

-spec maybe_else_03(foo | bar) -> foo.
maybe_else_03(X) ->
    maybe foo ?= X else _ -> error(badarg) end.

-spec maybe_else_04(foo | bar) -> foo.
maybe_else_04(X) ->
    maybe foo ?= X else bar -> foo end.

-spec maybe_else_05(foo | bar) -> foo.
maybe_else_05(X) ->
    maybe foo, bar, foo ?= X else bar -> foo end.

-spec maybe_else_06_fail() -> ok.
maybe_else_06_fail() ->
    maybe ok else bad -> bad end.

-spec maybe_07(string(), fun((string()) -> {ok, integer()} | {error, bad_int})) -> {ok, string()} | {error, bad_int}.
maybe_07(Str, Convert) ->
    maybe
        {ok, _} ?= Convert(Str),
        {ok, "ok"}
    end.

% from eqwalizer #55
-spec maybe_08(string()) -> {ok, string()} | {error, bad_int}.
maybe_08(Str) ->
    maybe
        {ok, Int} ?= convert_to_int(Str),
        {ok, integer_to_list(Int*2)}
    end.

-spec convert_to_int(string()) -> {ok, integer()} | {error, bad_int}.
convert_to_int(_) -> error('fun').

% from eqwalizer #51
% not possible to reason on length of lists without encoding it in the type itself
% last needs an nonempty list
-spec maybe_09_fail(list(binary())) -> {ok, binary()} | {error, any()}.
maybe_09_fail(Args) ->
    maybe
        true ?= (length(Args) =/= 0) orelse {error, empty_args},
        true ?= is_binary(lists:last(Args)) orelse {error, badargs},
        {ok, <<"ok">>}
    end.

% proposed alternative; other alternative is cast Args after the check to nonempty_list(binary())
-spec maybe_09(list(binary())) -> {ok, binary()} | {error, any()}.
maybe_09([]) -> {error, empty_args};
maybe_09(Args) ->
    maybe
        true ?= is_binary(lists:last(Args)) orelse {error, badargs},
        {ok, <<"ok">>}
    end.

