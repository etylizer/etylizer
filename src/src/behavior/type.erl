-module(type).
-vsn({2,0,0}).

% a type provides a basic set of functionalities 
% representations include:
% * intervals
% * products
% * arrows

-type x() :: term().

% any type can be checked for (structural) any
-callback is_any(x()) -> boolean().


% any type can be evaluated
% if empty, returns `empty`
% if non-empty, returns a witness for the type
-callback eval(x()) -> empty | {witness, x()}.

% any type can be checked for (semantic) emptiness
-callback is_empty(x()) -> boolean().

% create the empty type for the type set
-callback empty() -> x().
% create the any type for the type set
-callback any() -> x().

% union, intersect, diff, negate for the type set
-callback union(X, X) -> X when X :: x().
-callback intersect(X, X) -> X when X :: x().
-callback diff(X, X) -> X when X :: x().
-callback negate(X) -> X when X :: x().

