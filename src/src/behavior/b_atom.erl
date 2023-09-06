-module(b_atom).
-vsn({2,0,0}).

-callback finite([atom()]) -> term().
-callback cofinite([atom()]) -> term().
