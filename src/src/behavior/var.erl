-module(var).
-vsn({2,0,0}).

% TODO types
% every variable is distinct from all other created variables

% creates a new variable with a descriptive name
-callback new(string()) -> term().

% picks the smallest non-fixed variable among the positive and negative variables given
-callback smallest(term(), term(), sets:set()) -> term().

% implements the NTLV normalization rule for variables, returns a set of constraint sets
-callback normalize(term(), term(), term(), term(), function(), term()) -> list(list(term())).
