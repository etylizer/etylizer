-module(bits).

-compile(export_all).
-compile(nowarn_export_all).

foo() ->
    B = <<begin X = 1, X end, 17, 42>>,
    case B of
        <<Size:4, Data:Size/binary>> -> Data
    end,
    {X, B, Data}.
