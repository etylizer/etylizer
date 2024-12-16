-module(m4).

-compile(export_all).
-compile(nowarn_export_all).

-export_type([t/0, u/0]).

-type t() :: integer().
-type u() :: m3:u().
