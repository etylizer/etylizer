% minimize/3 takes a (multi-output) Boolean function described as a cube list and
% returns a (heuristically) smaller cube list that must denote the same function. 
% We check against a brute-force solution. 
% A cube list is fully characterised by its set of on points
% {Assignment, Leaf}, so two cube lists are equivalent iff those sets are equal.
% We get the on-set by enumerating the whole truth table.
-module(prop_dnf_minimizer).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

%% properties

%% minimize/3 denotes the same Boolean function as its input
prop_minimize_preserves_function() ->
    ?FORALL({NumVars, NumLeaves, OnSet}, problem(),
        on_points(NumVars, OnSet)
            =:= on_points(NumVars, dnf_minimizer:minimize(NumVars, NumLeaves, OnSet))).

%% every output cube is well formed 
%% no variable is forced to both 0 and 1 
%% all variable/leaf indices stay in range
prop_minimize_wellformed() ->
    ?FORALL({NumVars, NumLeaves, OnSet}, problem(),
        lists:all(
          fun({Pos, Neg, Leaves}) ->
              ordsets:is_disjoint(ordsets:from_list(Pos), ordsets:from_list(Neg))
                  andalso lists:all(fun(V) -> V >= 0 andalso V < NumVars end, Pos ++ Neg)
                  andalso lists:all(fun(L) -> L >= 0 andalso L < NumLeaves end, Leaves)
          end,
          dnf_minimizer:minimize(NumVars, NumLeaves, OnSet))).

%% truth table computation

%% a cube contributes a point for each leaf 
%% it drives whenever the assignment satisfies its positive and negative literals.
on_points(NumVars, Cubes) ->
    lists:usort(
      [ {Bits, Leaf}
        || Bits <- lists:seq(0, (1 bsl NumVars) - 1),
           {Pos, Neg, Leaves} <- Cubes,
           matches(Pos, Neg, Bits),
           Leaf <- Leaves ]).

matches(Pos, Neg, Bits) ->
    lists:all(fun(V) -> Bits band (1 bsl V) =/= 0 end, Pos) andalso
    lists:all(fun(V) -> Bits band (1 bsl V) =:= 0 end, Neg).

% generators

problem() ->
    ?LET(NumVars, integer(1, 5), % keep the truth table =< 32 rows
    % for type checking, minimizer inputs is heavly skewed towards single-output functions
    ?LET(NumLeaves, frequency([{80, 1}, {5, 2}, {5, 3}, {5, 4}, {5, 5}]),
    ?LET(Cubes, list(cube(NumVars, NumLeaves)),
        {NumVars, NumLeaves, Cubes}))).

% One literal per variable (1 / 0 / don't-care), so a generated
% cube can never be contradictory. That matches both how ty_rec/bdd build cubes
% (each variable appears at most once) and the positional encoding inside
% dnf_minimizer, where a variable set in both Pos and Neg would silently decode
% as don't-care rather than as the empty cube. 
% One output index per input cube mirrors how minimize/3 is used.
% bdd.hrl gives each distinct leaf its own output column and maps every DNF line
% to exactly one column.
cube(NumVars, NumLeaves) ->
    ?LET({Lits, Leaf},
         {vector(NumVars, oneof([pos, neg, dash])), integer(0, NumLeaves - 1)},
         {[V || {V, pos} <- lists:enumerate(0, Lits)],
          [V || {V, neg} <- lists:enumerate(0, Lits)],
          [Leaf]}).
