-module(numbers).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-type left_component() :: {left, integer()}.

-spec refine_01(left_component()) -> a | b | c.
refine_01({left, -1}) -> a;
refine_01({left, L}) when L < -1 -> b;
refine_01({left, L}) when L > -1 -> c.
