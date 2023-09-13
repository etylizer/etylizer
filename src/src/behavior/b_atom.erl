-module(b_atom).

-callback finite([atom()]) -> term().
-callback cofinite([atom()]) -> term().
