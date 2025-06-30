-module(dnf_ty_bitstring).

% currently only supported: bitstring yes/no

compare(X, X) -> eq; compare(1, 0) -> gt; compare(0, 1) -> lt.
equal(X, Y) -> X =:= Y.
empty() -> 0.
any() -> 1.
union(X, Y) -> erlang:max(X, Y).
intersect(X, Y) -> erlang:min(X, Y).
difference(_, 1) -> 0; difference(X, _) -> X.
negate(1) -> 0; negate(0) -> 1.
is_any(1) -> true; is_any(_) -> false.
is_empty(0, S) -> {true, S}; is_empty(_, S) -> {false, S}.
substitute(_,X,_,_) -> X.
% there is nothing to substitute in a ty_bool
map_pi(_) -> #{}.
has_ref(_,_) -> false.
raw_transform(T, Op) -> transform(T, Op).
transform(0, #{empty := E}) -> E();
transform(1, #{any := A}) -> A().

normalize(Dnf, _Fixed, ST) ->
  % Fig. 3 Line 3
  case is_empty(Dnf, #{}) of
    {true, _} -> {[[]], ST};
    {false, _} -> {[], ST}
  end.

unparse(0, ST) -> {{predef, none}, ST};
unparse(1, ST) -> {{predef, any}, ST}.

all_variables(_, _) -> sets:new().
