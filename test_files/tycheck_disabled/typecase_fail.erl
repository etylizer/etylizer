-module(typecase_fail).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec foo(number()) -> number(); (string()) -> string().
foo(X) when is_integer(X) -> "foo";
foo(X) -> string:length(X).
