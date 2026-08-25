-module(issue_235_op_tyvars).

-compile(export_all).
-compile(nowarn_export_all).

% Regression test for issue #235

-spec same() -> boolean().
same() ->
  true andalso true =/= ok.

-spec two_andalso() -> {1, hello}.
two_andalso() ->
    X = true andalso 1,
    Y = true andalso hello,
    {X, Y}.

-spec two_orelse() -> {1, hello}.
two_orelse() ->
    X = false orelse 1,
    Y = false orelse hello,
    {X, Y}.
