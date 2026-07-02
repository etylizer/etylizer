-module(user).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% USER-DEFINED TYPES %%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%% RECURSIVE TYPES    %%%%%%%%%%%%%%%%%%%%%%%%
 
% user-defined type
-type user_t_01() :: foobar.
-spec user_01() -> user_t_01().
user_01() -> foobar.

% argument
-type user_t_02(X) :: X.
-spec user_02() -> user_t_02(foobar).
user_02() -> foobar.

% recursive type, unfold static 1
-type user_t_03a(X) :: nil | {X, user_t_03a(X)}.
-spec user_03a() -> user_t_03a(foo).
user_03a() -> {foo, nil}.

% recursive type, unfold static 1
-type user_t_03(X) :: nil | {X, user_t_03(X)}.
-spec user_03(non_neg_integer()) -> user_t_03(foo).
user_03(0) -> nil;
user_03(_) -> {foo, nil}.

% recursive type, unfold static 2
-type user_t_04(X) :: nil | {X, user_t_04(X)}.
-spec user_04(non_neg_integer()) -> user_t_04(foo).
user_04(0) -> nil;
user_04(1) -> {foo, nil};
user_04(_) -> {foo, {foo, nil}}.

-spec user_04_fail(non_neg_integer()) -> user_t_04(foo).
user_04_fail(0) -> nil;
user_04_fail(1) -> {foo, nil};
user_04_fail(_) -> {foo, {fo, nil}}.

% TODO we can't check this 
% '-' operation does not ensure that I-1 is still a non_neg_integer()
% recursive type, unfold recursive
%-type user_t_05(X) :: nil | {X, user_t_05(X)}.
%-spec user_05(non_neg_integer()) -> user_t_05(foo).
%user_05(0) -> nil;
%user_05(I) -> {foo, user_05(I-1)}.

% recursive type apply once
-type user_t_06(X) :: nil | {X, user_t_06(X)}.
-spec user_06(boolean()) -> user_t_06(foo).
user_06(true) -> nil;
user_06(false) -> {foo, user_06(true)}.

% recursive type descend recursive
-type user_t_07(X) :: nil | {X, user_t_07(X)}.
-spec user_07(user_t_07(foo)) -> integer().
user_07(nil) -> 1;
user_07({foo, X}) -> user_07(X).

% #182
-type user_t_08() :: {a | user_t_08()}.
-spec user_08(user_t_08()) -> user_t_08().
user_08(Forms) -> user_08(Forms).

% #226
-type user_t_09() :: {{user_t_09()} | b}.
-spec user_09_fail() -> user_t_09().
user_09_fail() -> ok.

-type user_t_10() :: {foo} | {user_t_10()}.
-spec user_10(user_t_10()) -> user_t_10().
user_10({foo}) -> {foo};
user_10(T) -> T.
