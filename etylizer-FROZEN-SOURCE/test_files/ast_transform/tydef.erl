-module(tydef).

-export_type([t1/2, t2/2]).

-type t1(A, B) :: {A, B}.
-type t2(B, A) :: {A, B}.
