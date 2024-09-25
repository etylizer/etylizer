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
-spec user_03(pos_integer()) -> user_t_03(foo).
user_03(0) -> nil;
user_03(_) -> {foo, nil}.

% recursive type, unfold static 2
-type user_t_04(X) :: nil | {X, user_t_04(X)}.
-spec user_04(pos_integer()) -> user_t_04(foo).
user_04(0) -> nil;
user_04(1) -> {foo, nil};
user_04(_) -> {foo, {foo, nil}}.

% recursive type, unfold recursive
-type user_t_05(X) :: nil | {X, user_t_05(X)}.
-spec user_05(pos_integer()) -> user_t_05(foo).
user_05(0) -> nil;
user_05(I) -> {foo, user_05(I-i)}.

% recursive type fail 
-type user_t_06(X) :: nil | {X, user_t_06(X)}.
-spec user_06_fail(integer()) -> user_t_06(foo).
user_06_fail(0) -> nil;
user_06_fail(I) -> {foo, user_06_fail(I-1)}.

