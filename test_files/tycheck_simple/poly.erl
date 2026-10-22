-module(poly).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

-spec poly_01(T) -> T.
poly_01(X) -> X.

-spec poly_02(T) -> T.
poly_02(X) ->
  case X of
    Y -> Y
  end.

-spec poly_03(T, any()) -> T.
poly_03(X, _Y) -> X.

% The first branch of the case is not redundant
-spec poly(T) -> T.
poly(X) ->
    case X of
        1 -> X;
        _ -> X
    end.

-spec poly_inter(T) -> T; (T) -> T.
poly_inter(X) ->
    case X of
        1 -> X;
        _ -> X
    end.

% Only matches tuples
-spec foo5_fail(Foo) -> Foo.
foo5_fail({_}) -> ok.

% A result-only variable with a term() bound is term(), not a type of the caller's choice
-spec result_term(integer()) -> R when R :: term().
result_term(X) -> X.

-spec result_term_fail(integer()) -> atom().
result_term_fail(X) -> result_term(X).

-spec result_term_case(integer()) -> integer().
result_term_case(X) -> H = result_term(X), if H > 0 -> 1; true -> 2 end.
