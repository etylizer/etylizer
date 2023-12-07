-module(my_and_fail).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec my_and(any(), T) -> T | false.
my_and(true, _X) -> true;
my_and(false, _) -> false;
my_and(_, false) -> false.
% not exhaustive, e.g. for (ok, 42)
