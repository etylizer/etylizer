% ERROR
% test_files/tycheck/type_error_msgs/invalid_record_update.erl:14:25: Type error: in foo/1, expression failed to type check
-module(invalid_record_update).

-compile(export_all).
-compile(nowarn_export_all).

-record(r, {a :: integer(), b :: atom()}).

-spec id(#r{}) -> #r{}.
id(R) -> R.

-spec foo(#r{}) -> #r{}.
foo(R) -> (id(R))#r{a = bar}. % error here, at the value of the field
