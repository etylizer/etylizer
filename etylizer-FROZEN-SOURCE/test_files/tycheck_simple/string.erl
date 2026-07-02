-module(string).

-compile([export_all, nowarn_export_all]).


% === test cases for stdlib Erlang string functions

% os:getenv needs nonempty_string, string functions need to support nonempty_string overload
-spec to_upper2(string()) -> string(); (nonempty_string()) -> nonempty_string().
to_upper2(_) -> error(badarg).
-spec string_01() -> boolean().
string_01() ->
    case os:getenv(to_upper2("alg")) of "v1" -> true; _ -> false end.
