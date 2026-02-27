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

-spec list_01_fail(
        fun((nonempty_list(A), list(A)) -> A),
        {list(Item), list(Item)}) -> Item.
list_01_fail(_Fun, {[],[]}) -> error(todo); % both R and F are non-empty in the next branch
list_01_fail(Fun, {R,F}) when is_list(R), is_list(F) -> Fun(R, F).

%%%%%%%%%%%%%%%%%%%%%%%% LIST1, LIST2, LIST3, LIST1STAR %%%%%%%%%%%%%%%%%%%%%%%

% list1: exactly one element
-spec list1_01() -> etylizer:list1(integer()).
list1_01() -> [1].

-spec list1_02() -> etylizer:list1(atom()).
list1_02() -> [hello].

-spec list1_03_fail() -> etylizer:list1(integer()).
list1_03_fail() -> [1, 2].

-spec list1_04_fail() -> etylizer:list1(integer()).
list1_04_fail() -> [].

-spec list1_05_fail() -> etylizer:list1(integer()).
list1_05_fail() -> [hello].

% list1 in argument position
-spec list1_06(etylizer:list1(integer())) -> integer().
list1_06([X]) -> X.

% list2: exactly two elements
-spec list2_01() -> etylizer:list2(integer(), atom()).
list2_01() -> [1, hello].

-spec list2_02() -> etylizer:list2(atom(), atom()).
list2_02() -> [a, b].

-spec list2_03_fail() -> etylizer:list2(integer(), atom()).
list2_03_fail() -> [1].

-spec list2_04_fail() -> etylizer:list2(integer(), atom()).
list2_04_fail() -> [1, 2, 3].

-spec list2_05_fail() -> etylizer:list2(integer(), atom()).
list2_05_fail() -> [hello, world].

% list2 in argument position
-spec list2_06(etylizer:list2(integer(), atom())) -> {integer(), atom()}.
list2_06([X, Y]) -> {X, Y}.

% list3: exactly three elements
-spec list3_01() -> etylizer:list3(integer(), atom(), float()).
list3_01() -> [1, hello, 2.0].

-spec list3_02_fail() -> etylizer:list3(integer(), atom(), float()).
list3_02_fail() -> [1, hello].

-spec list3_03_fail() -> etylizer:list3(integer(), atom(), float()).
list3_03_fail() -> [1, hello, 2.0, extra].

% list3 in argument position
-spec list3_04(etylizer:list3(integer(), atom(), float())) -> {integer(), atom(), float()}.
list3_04([X, Y, Z]) -> {X, Y, Z}.

% list1star: first element of type T, then arbitrary many Us
-spec list1star_01() -> etylizer:list1star(integer(), atom()).
list1star_01() -> [1].

-spec list1star_02() -> etylizer:list1star(integer(), atom()).
list1star_02() -> [1, hello].

-spec list1star_03() -> etylizer:list1star(integer(), atom()).
list1star_03() -> [1, hello, world].

-spec list1star_04_fail() -> etylizer:list1star(integer(), atom()).
list1star_04_fail() -> [].

-spec list1star_05_fail() -> etylizer:list1star(integer(), atom()).
list1star_05_fail() -> [hello].

% list1star in argument position
-spec list1star_06(etylizer:list1star(integer(), atom())) -> integer().
list1star_06([X | _]) -> X.

