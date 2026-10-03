% ERROR
% test_files/tycheck/type_error_msgs/invalid_record_default.erl:8:41: Type error: in foo/0, expression failed to type check
-module(invalid_record_default).

-compile(export_all).
-compile(nowarn_export_all).

-record(r, {a = 0 :: integer(), b = {x, 1} :: {atom(), atom()}}). % error here, in the default of b

-spec foo() -> #r{}.
foo() -> #r{}.
