-module(basic_types).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% ATOMS %%%%%%%%%%%%%%%%%%%%%%%s
-spec atom_01() -> foobar.
atom_01() -> foobar.

-spec atom_02() -> atom().
atom_02() -> foobar.

-spec atom_03_fail() -> integer().
atom_03_fail() -> foobar.

-spec atom_04_fail() -> foobar.
atom_04_fail() -> 1.

-spec atom_05_fail() -> atom().
atom_05_fail() -> 1.

-spec atom_06_fail() -> foobar.
atom_06_fail() -> spam.

% Chars
-spec char_01() -> $a.
char_01() -> $a.

-spec char_02() -> char().
char_02() -> $a.

-spec char_03() -> integer().
char_03() -> $a.

-spec char_04_fail() -> atom().
char_04_fail() -> $a.

-spec char_05_fail() -> $a.
char_05_fail() -> foobar.

-spec char_06_fail() -> $a.
char_06_fail() -> 1.

-spec char_07() -> $a.
char_07() -> 97. % ascii code for a

-spec char_08_fail() -> char().
char_08_fail() -> foobar.

-spec char_09_fail() -> $a.
char_09_fail() -> $b.

%%%%%%%%%%%%%%%%%%%%%%%% INTEGERS %%%%%%%%%%%%%%%%%%%%%%%

-spec integer_01() -> 42.
integer_01() -> 42.

-spec integer_02() -> integer().
integer_02() -> 42.

-spec integer_03_fail() -> atom().
integer_03_fail() -> 42.

-spec integer_04_fail() -> 42.
integer_04_fail() -> foobar.

-spec integer_05_fail() -> integer().
integer_05_fail() -> foobar.

-spec integer_06_fail() -> 42.
integer_06_fail() -> 43.

-spec integer_07() -> number().
integer_07() -> 42.

%%%%%%%%%%%%%%%%%%%%%%%% FLOATS %%%%%%%%%%%%%%%%%%%%%%%

-spec float_01() -> float().
float_01() -> 3.14.

-spec float_02() -> float().
float_02() -> 42.0.

-spec float_03() -> number().
float_03() -> 3.14.

-spec float_04_fail() -> float().
float_04_fail() -> "bass".

-spec float_05_fail() -> atom().
float_05_fail() -> 3.14.

%%%%%%%%%%%%%%%%%%%%%%%% STRINGS %%%%%%%%%%%%%%%%%%%%%%%

-spec string_01() -> string().
string_01() -> "bass".

-spec string_02() -> string().
string_02() -> "".

-spec string_03() -> [].
string_03() -> "".

-spec string_04() -> [char()].
string_04() -> "bass".

-spec string_05_fail() -> string().
string_05_fail() -> 1.

-spec string_06_fail() -> [atom()].
string_06_fail() -> "bass".

-spec string_07() -> [integer()].
string_07() -> "bass".

-spec string_08_fail() -> 1.
string_08_fail() -> "bass".
