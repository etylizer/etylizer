-module(nominal).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-nominal meter() :: integer().
-nominal foot() :: integer().

-type regular_int() :: integer().
-type regular_nominal_meter() :: meter().

%%%%%%%%%%%%%%%%%%%%%%%% BASIC IDENTITY %%%%%%%%%%%%%%%%%%%%%%%

% Same nominal type: should pass
-spec same_nominal_01(meter()) -> meter().
same_nominal_01(X) -> X.

-spec same_nominal_02(meter()) -> regular_nominal_meter().
same_nominal_02(X) -> X.

-spec same_nominal_03(regular_nominal_meter()) -> meter().
same_nominal_03(X) -> X.

-spec same_nominal_04(regular_nominal_meter()) -> regular_nominal_meter().
same_nominal_04(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% INCOMPATIBLE NOMINALS %%%%%%%%%%%%%%%%%%%%%%%

% Different nominal types: should fail
-spec different_nominal_01_fail(meter()) -> foot().
different_nominal_01_fail(X) -> X.

% Different nominal types: should fail
-spec different_nominal_02_fail(foot()) -> meter().
different_nominal_02_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% STRUCTURAL COMPATIBILITY %%%%%%%%%%%%%%%%%%%%%%%

% Nominal to structural
-spec nominal_to_structural_01(meter()) -> integer().
nominal_to_structural_01(X) -> X.

% Structural to nominal
-spec structural_to_nominal_01(integer()) -> meter().
structural_to_nominal_01(X) -> X.

% Nominal to regular type alias: should pass
-spec nominal_to_alias_01(meter()) -> regular_int().
nominal_to_alias_01(X) -> X.

% Regular type alias to nominal: should pass
-spec alias_to_nominal_01(regular_int()) -> meter().
alias_to_nominal_01(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% COMPOUND TYPES %%%%%%%%%%%%%%%%%%%%%%%

-spec tuple_same_01({meter(), foot()}) -> {meter(), foot()}.
tuple_same_01(X) -> X.

-spec tuple_different_01_fail({meter()}) -> {foot()}.
tuple_different_01_fail(X) -> X.

%%%%%%%%%%%%%%%%%%%%%%%% FUNCTION CALLS %%%%%%%%%%%%%%%%%%%%%%%

-spec call_same_01(meter()) -> meter().
call_same_01(X) -> same_nominal_01(X).

-spec nominal_add_01(meter(), meter()) -> integer().
nominal_add_01(X, Y) -> X + Y.

%%%%%%%%%%%%%%%%%%%%%%%% MIXED %%%%%%%%%%%%%%%%%%%%%%%

-spec mixed_tuple_01({meter(), integer()}) -> {meter(), integer()}.
mixed_tuple_01(X) -> X.

-spec nominal_any_01(meter()) -> any().
nominal_any_01(X) -> X.
