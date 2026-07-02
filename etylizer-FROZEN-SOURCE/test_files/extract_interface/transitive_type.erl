-module(transitive_type).

-export_type([exported_type/0]).

-type exported_type() :: local_type_1().

-type local_type_1() :: local_type_2().
-type local_type_2() :: integer().
