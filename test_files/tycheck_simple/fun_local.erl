-module(fun_local).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% LOCAL FUNS %%%%%%%%%%%%%%%%%%%%%%%

-spec fun_local_01() -> integer().
fun_local_01() ->
    F = fun(X, Y) -> X + Y end,
    F(1, 2).

-spec fun_local_02() -> integer().
fun_local_02() ->
    F = fun Add(X) ->
        case X of
            0 -> 0;
            Y -> Y + Add(X - 1)
        end
        end,
    F(3).
%
% same as fun_local_02 but transformed
% such that there are no n-tuples and n-functions anymore
-spec fun_local_02_plus() -> integer().
fun_local_02_plus() ->
    F = fun Add(X) ->
        case X of
            0 -> 0;
            Y -> my_plus({Y, Add(my_plus({X, -1}))})
        end
        end,
    F(3).

-spec my_plus({integer(), integer()}) -> integer(); ({float(), integer()}) -> float(); ({integer(), float()}) -> float(); ({float(), float()}) -> float().
my_plus({A, B}) -> A + B.

-spec fun_local_03() -> integer().
fun_local_03() ->
    F = fun
            Add(0) -> 0;
            Add(X) -> X + Add(X - 1)
        end,
    F(3).

-spec fun_local_03_fail() -> integer().
fun_local_03_fail() ->
    F = fun
            Add(0) -> blub;
            Add(X) -> X + Add(X - 1)
        end,
    F(3).

-spec fun_local_03b_fail() -> integer().
fun_local_03b_fail() ->
    F = fun
            Add(0) -> 0;
            Add(X) -> X ++ Add(X - 1)
        end,
    F(3).

-spec fun_local_04() -> integer().
fun_local_04() ->
    F = fun
            Add(X) when X =:= 0 -> 0;
            Add(X) -> X + Add(X + 1)
        end,
    F(3).

-spec fun_local_05_fail(integer()) -> integer().
fun_local_05_fail(X) ->
    F = fun(Y) -> X + Y end,
    F("foo").

-spec fun_local_06(atom()) -> foobar.
fun_local_06(A) ->
  F = fun(X) ->
        case X of
            spam -> foobar;
            _ -> foobar
        end
      end,
  F(A).

-spec fun_local_06_fail() -> foobar.
fun_local_06_fail() ->
  F = fun(X) ->
        case X of
            spam -> foobarx;
            _ -> foobar
        end
      end,
  F(spam).

-spec fun_local_06b_fail() -> foobar.
fun_local_06b_fail() ->
  F = fun(X) ->
        case X of
            spam -> foobar;
            _ -> foobarx
        end
      end,
  F(spam).

-spec fun_local_06c_fail() -> foobar.
fun_local_06c_fail() ->
  F = fun(X) ->
        case X of
            spam -> foobar;
            _ -> foobar % redundant case
        end
      end,
  F(spam).

-spec fun_local_07(1) -> a; (2) -> b.
fun_local_07(X) ->
    F = fun(Y) ->
            case Y of
                1 -> a;
                2 -> b
            end
        end,
    F(X).

-spec fun_local_07_fail(1) -> a; (2) -> b.
fun_local_07_fail(X) ->
    F = fun(Y) ->
            case Y of
                1 -> c; % result c has wrong type (must be a)
                2 -> b
            end
        end,
    F(X).

fun_local_08() ->
    fun
        Add(_) when 0 =:= 0 -> 0;
        Add(X) -> Add(X)
    end.
