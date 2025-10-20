-module(list).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% CONS, NIL %%%%%%%%%%%%%%%%%%%%%%%

-spec cons_01() -> list(integer()).
cons_01() -> [1 | [2 | []]].

-spec cons_02() -> list(any()).
cons_02() -> [1 | ["foo" | []]].

-spec cons_03() -> list(string() | integer()).
cons_03() -> [1 | ["foo" | []]].

-spec cons_04_fail() -> list(integer()).
cons_04_fail() -> [1 | [2 | 3]].

-spec cons_05() -> list().
cons_05() -> [1 | [2 | []]].

-spec cons_06_fail() -> [].
cons_06_fail() -> [1 | [2 | []]].

-spec nil_01() -> list(none()).
nil_01() -> [].

-spec nil_02() -> nil().
nil_02() -> [].

-spec nil_03() -> list().
nil_03() -> [].

-spec nil_04() -> list(any()).
nil_04() -> [].

-spec nil_05_fail() -> integer().
nil_05_fail() -> [].

-spec list_pattern_01(list(integer())) -> integer().
list_pattern_01(L) ->
    case L of
        [] -> 1;
        [X | _] -> X
    end.

-spec list_pattern_02(list(integer())) -> integer().
list_pattern_02(L) ->
    case L of
        [] -> 1;
        [_X, Y | _] -> Y;
        [X | _] -> X
    end.

-spec list_pattern_03_fail(list(integer())) -> integer().
list_pattern_03_fail(L) ->
    case L of
        % not exhaustive
        [X | _] -> X
    end.

-spec list_pattern_03(nonempty_list(integer())) -> integer().
list_pattern_03(L) ->
    case L of
        [X | _] -> X
    end.

-spec list_pattern_04_fail(list(integer())) -> integer().
list_pattern_04_fail(L) ->
    case L of
        [] -> 1;
        % not exhaustive
        [_X, Y | _] -> Y
    end.

-spec list_pattern_04b_fail(list(integer())) -> integer().
list_pattern_04b_fail(L) ->
    case L of
        [] -> 1;
        % not exhaustive
        [_X, []] -> 2
    end.

-spec list_pattern_05_fail(list(integer())) -> integer().
list_pattern_05_fail(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2 % not exhaustive
    end.

-spec list_pattern_06_fail(list(integer())) -> integer().
list_pattern_06_fail(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [_X] -> 3 % not exhaustive
    end.

-spec list_pattern_07(list(integer())) -> integer().
list_pattern_07(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [_X | _] -> 3
    end.

-spec list_pattern_08_fail(list(integer())) -> integer().
list_pattern_08_fail(L) ->
    case L of
        [] -> 1;
        [1 | _] -> 2;
        [1, 2 | _] -> 3; % redundant
        _ -> 4
    end.

-spec list_pattern_09_fail(nonempty_list(integer())) -> integer().
list_pattern_09_fail(L) ->
    case L of
        [_] -> 2;
        [_ | A] -> 
          case A of
            [] -> 3; % redundant, can't be [] because of [_] branch
            _ -> 4 
          end
    end.

-spec list_pattern_10_fail_h(nonempty_list(_)) -> integer().
list_pattern_10_fail_h([_ | _]) -> 42.

-spec list_pattern_10_fail() -> integer().
list_pattern_10_fail() -> 
  Fun = fun _F([_ | Vs]) -> list_pattern_10_fail_h(Vs) end,
  Fun([x | []]).

-spec list_pattern_11(list(V)) -> {ok, V} | error.
list_pattern_11([]) -> error;
list_pattern_11([V | []]) -> {ok, V};
list_pattern_11([_ | Rest]) ->
    case list_pattern_11(Rest) of
        {ok, _} -> error;
        _ -> error
    end.

-spec list_pattern_12(string()) -> bad | bad2.
list_pattern_12(S) ->
  case S of
    "trace" -> bad;
    "trace2" -> bad2;
    _ -> bad
  end.
