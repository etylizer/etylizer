-module(numbers).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-type left_component() :: {left, integer()}.
-type right_component() :: {right, integer()}.

-spec refine_01(left_component()) -> a | b | c.
refine_01({left, -1}) -> a;
refine_01({left, L}) when L < -1 -> b;
refine_01({left, L}) when L > -1 -> c.

-spec refine_02({range, integer(), integer()} | any_int | left_component() | right_component()) -> any().
refine_02(any_int) -> a;
refine_02({range, _, _}) -> a;
refine_02({left, -1}) -> a;
refine_02({right, 1}) -> a;
refine_02({left, L}) when L < -1 -> a;
refine_02({left, L}) when L > -1 -> a;
refine_02({right, R}) when R > 1 -> a;
refine_02({right, R}) when R < 1 -> a.
