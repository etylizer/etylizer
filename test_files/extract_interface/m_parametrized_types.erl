-module(parametrized_types).

-export([exported_function/1]).

-type parametrized_type(T) :: [T].
-type parameter_type() :: integer().

-spec exported_function(parametrized_type(parameter_type())) -> integer().
exported_function(List) ->
    [Head | _Tail] = List,
    Head.
