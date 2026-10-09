-module(remote_type_argument).

-export_type([exported_type/0]).

-type wrapper(T) :: {ok, T}.
-type local_type() :: integer().

-type exported_type() :: wrapper(sets:set(local_type())).
