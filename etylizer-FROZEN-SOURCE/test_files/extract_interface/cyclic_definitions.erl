-module(cyclic_definitions).

-export_type([foo/0]).

-type foo() :: foo().
