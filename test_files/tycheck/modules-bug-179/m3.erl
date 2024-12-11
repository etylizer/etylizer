-module(m3).

-compile(export_all).
-compile(nowarn_export_all).

-export_type([t/0, u/0]).

-type t() :: m4:t().
-type u() :: atom().
