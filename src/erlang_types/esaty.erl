-module(esaty).

%% SaTy, SA(T)isfiability of TYpe constraints: deciding the satisfiability
%% of a tallying problem by a single-path search *inside* normalization.
%%
%% Tallying (etally, v1..v6) decides "is there a solution?" in two phases
%% that both materialize every solution. Phase 1 normalizes each constraint
%% S <= T into the complete set of constraint sets that make S \ T empty --
%% bdd.hrl meets the per-line results, dnf_ty_tuple and dnf_ty_function meet
%% and join their decompositions -- and phase 2 merges those sets with meet
%% (a cartesian product pruned by subsumption), join and saturation. The
%% answer is whether the final set is non-empty; the cost is the width of
%% every intermediate set. That is how a model counter works.
%%
%% SaTy never builds a set of constraint sets. "Make T empty under the
%% current bounds C" is a *goal* that is searched, one choice at a time, by
%% an iterative engine over two stacks: an AND (every DNF line, every tuple
%% component) pushes the rest of the conjunction onto the pending
%% stack, an OR (some component empty, some negative arrow refuting the
%% line) is a decision that pushes its remaining alternatives onto the
%% choice stack and backtracks, and a line emits ONE one-sided bound -- alpha <=
%% single(...) or single(...) <= alpha, the NTLV rule -- which is merged
%% into C on the spot. When the merge tightens an existing bound, the
%% consequence that saturation would add later is itself an empty goal run
%% right away, on the tightened pair: CL \ (CU & U) (resp. (CL | L) \ CU).
%% The search succeeds when Pending is exhausted: every line consumed, every
%% consequence established, C saturated by construction. It fails when the
%% choice stack is: every alternative refuted. The correspondence with a SAT
%% solver:
%%
%%   partial assignment      the bound map C : variable -> {Lower, Upper}
%%   literal                 one one-sided bound from the NTLV rule
%%   decision                an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a tightened pair
%%   conflict                a line that cannot be made empty under C
%%   conflict analysis       the reason set of a failure: the decisions the
%%                           bounds it read depend on
%%   backjumping             a decision that a failure does not depend on
%%                           does not try its other alternatives
%%   model                   Pending exhausted
%%
%% The engine. Goals are data, and the search is three mutually
%% tail-recursive functions, so it runs in constant Erlang stack however
%% deep the path:
%%
%%   goal/3      runs a goal under the current bounds, cache and path
%%   continue/1  the goal succeeded: the next goal on Pending runs -- the
%%               remaining conjuncts of an enclosing conjunction
%%   backtrack/2 the goal failed: the choice stack is unwound until a
%%               decision the failure depends on has an alternative left
%%
%% Pending is what is left to do when a goal succeeds, and the choice stack
%% is what a failure returns through: a decision for every OR on the path,
%% with the alternatives it has left. A decision keeps the bounds, the cache
%% and Pending it was made under, so its next alternative starts from them.
%% Pending has to be kept and cannot be read off a single stack shared with
%% the decisions: for A = A1 | A2 followed by B, the decision for A2 is
%% pushed above B, A1 succeeds and B is popped, B fails, and the alternative
%% A2 has to run B again, which is gone from Pending. Pending is a list
%% shared by every alternative, so keeping it costs one word.
%%
%% The reasons are what makes the search tractable where normalize is: a
%% tuple or function decomposition has many independent decisions, and a
%% later constraint that fails for reasons of its own must not make the
%% search enumerate their product. Every bound piece carries the decisions
%% it depends on (the path of decisions above the line that emitted it), a
%% consequence goal inherits the reasons of both pieces it relates, a ground
%% line that cannot be made empty fails with the reasons of its goal, and a
%% decision whose alternative fails for a reason it is not part of fails
%% with that reason at once.
%%
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded in the state
%% along Pending: a recursive type met again is assumed empty, and a sub-goal
%% met again on the same path is skipped since its bounds are already in C.
%% Backtracking discards X with the path.
%%
%% SaTy searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions, with prunings that lose no answer. A goal achieved on the
%% path is not redone (C already lies inside it, the other alternatives only
%% tighten C, and any path below a tighter set has a solution that also
%% satisfies C and the pending goals). And a backjump skips alternatives
%% only when the failure read no bound that the decision produced, so the
%% same failure exists under every alternative.

-export([is_satisfiable/2]).

-include("constraints.hrl").

% data structure used for caching
-type memo_set(A) :: #{A => []}.

% problem input shape
-type input_constraints() :: [{ty:type(), ty:type()}].

% the decisions a bound piece, a goal or a failure depends on
-type reason() :: #{integer() => []}.

% the current bounds of every variable constrained so far,
% each side with the decisions its pieces depend on
% if the inputs constraints are satisfiable,
% these bounds denote one valid substitution (pre-solved) substitution
-type bounds() :: #{variable() => {ty:type(), ty:type(), reason(), reason()}}.

% the cache for the coinductive hypothesis,
% is modified when empty(T) starts
-type cache() :: memo_set({node, ty:type()}).

% conjunction of goals
-type conjuncts() :: [goal()].

% A search goal
-type goal() :: 
    {empty, ty:type()} % make the node empty
  | {line, {[variable()], [variable()], ty_rec:type()}} % a DNF line of a node
  | {all, conjuncts()} % a conjunction of goals; disjunctions are not part of goals
  % decomposition of tuples
  | {tuple_line, tuple_dnf_line()}
  | {phi_tuple, [ty:type()], [ty_tuple:type()]}
  % decomposition of functions
  | {fun_line, function_dnf_line()}
  | {fun_explore, ty:type(), ty:type(), [ty_function:type()]}
  % decomposition of maps
  | {map_line, map_dnf_line()}.

% pending is the rest of the search after a goal succeeds,
% each goal with the decisions it depends on
-type pending() :: [{goal(), reason()}].

% disjunctions are the decisions to backtrack to
-type choice() :: {decide, untried_alternatives(), bounds(), cache(), pending(), reason(), integer(), reason()}.
-type untried_alternatives() :: [goal()]. % can be empty
-type choices() :: [choice()].

-record(state, {
  % immutable, set once at the beginning, not used for bounds()
  fixed :: monomorphic_variables(),
  % bounds of all poly variables which get refined 
  % until either a conflict occurs and the search backtracks to the latest decision it depends on (restoring bounds),
  % or all goals succeed and the refined bounds can be used to compute a valid (i.e. saturated) substitution
  bounds :: bounds(),
  % cache used for coinductive hypothesis
  cache :: cache(),
  % worklist for goals to be done
  pending :: pending(),
  % choices for backtracking
  choices :: choices()
}).
-type state() :: #state{}.

% all input constraints empty -> satisfiable
-spec is_satisfiable(input_constraints(), monomorphic_variables()) -> boolean().
is_satisfiable(Constraints, Fixed) ->
  Goals = [{empty, ty_node:difference(S, T)} || {S, T} <- Constraints],
  St = #state{fixed = Fixed, bounds = #{}, cache = #{}, pending = [{{all, Goals}, #{}}], choices = []},
  continue(St).

% run one goal under the decisions its existence depends on
-spec goal(goal(), reason(), state()) -> boolean().
goal(Goal, Path, St) ->
  case Goal of
    {empty, T} -> empty(T, Path, St);
    {line, L} -> line(L, Path, St);
    {all, Goals} -> all_of(Goals, Path, St);
    {tuple_line, L} -> tuple_line(L, Path, St);
    {phi_tuple, BigS, Neg} -> phi(BigS, Neg, Path, St);
    {fun_line, L} -> function_line(L, Path, St);
    {fun_explore, T1, T2, P} -> explore(T1, T2, P, Path, St);
    {map_line, L} -> map_line(L, Path, St)
  end.

% run the next pending goal under the decisions it depends on
% if there are no pending goals, the search has succeeded
-spec continue(state()) -> boolean().
continue(#state{pending = []}) -> true;
continue(St = #state{pending = [{G, Path} | Pending]}) ->
  goal(G, Path, St#state{pending = Pending}).

% when there is a conflict for reason R,
% the choice stack is unwound until a decision R depends on has an alternative left.
% if there is none, the constraints are unsatisfiable.
-spec backtrack(reason(), state()) -> boolean().
backtrack(_R, #state{choices = []}) -> false;
backtrack(R, St = #state{choices = [{decide, UntriedAlternatives, C, Cache, Pending, Path, D, Acc} | Ch]}) ->
  case R of
    #{D := _} ->
      decide(UntriedAlternatives, Path, D, maps:merge(Acc, R), St#state{bounds = C, cache = Cache, pending = Pending, choices = Ch});
    _ ->
      backtrack(R, St#state{choices = Ch})
  end.

% a conjunction: 
% runs the first goal now, and remembers the rest in pending (for success)
% under the decisions the conjunction depends on
% an empty conjunction holds
-spec all_of(conjuncts(), reason(), state()) -> boolean().
all_of([], _Path, St) -> continue(St);
all_of([G], Path, St) -> goal(G, Path, St);
all_of([G | Gs], Path, St = #state{pending = Pending}) ->
  goal(G, Path, St#state{pending = [{{all, Gs}, Path} | Pending]}).

% a disjunction: a decision
% runs the first goal now, and remembers the rest 
% with the current bounds, cache, and pending in the decision (for failure)
% an empty disjunction is a conflict
% an alternative that fails for a reason this decision is not part of fails
% the decision at once, since the same failure exists under every other
% alternative; otherwise the next alternative is tried, and the reasons of
% all of them, minus the decision itself, are the reason the decision fails
-spec any_of(untried_alternatives(), reason(), state()) -> boolean().
any_of([], Path, St) -> backtrack(Path, St);
any_of(Goals, Path, St) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, Path, D, #{}, St).

-spec decide(untried_alternatives(), reason(), integer(), reason(), state()) -> boolean().
decide([], _Path, D, Acc, St) ->
  backtrack(maps:remove(D, Acc), St);
decide([G | Gs], Path, D, Acc, St = #state{bounds = C, cache = Cache, pending = Pending, choices = Ch}) ->
  goal(G, Path#{D => []}, St#state{choices = [{decide, Gs, C, Cache, Pending, Path, D, Acc} | Ch]}).

% make type T empty
-spec empty(ty:type(), reason(), state()) -> boolean().
empty(T, Path, St = #state{cache = Cache}) ->
  case Cache of
    #{{node, T} := _} -> continue(St);
    _ ->
      Lines = dnf_ty_variable:minimize_dnf(ty_node:load(T)),
      all_of([{line, L} || L <- Lines], Path, St#state{cache = Cache#{{node, T} => []}})
  end.

% single out the smallest polymorphic variable 
% into one one-sided bound
% a line without one goes to the constructor level.
-spec line({[variable()], [variable()], ty_rec:type()}, reason(), state()) -> boolean().
line({[], [], Leaf}, Path, St) ->
  constructors_empty(Leaf, Path, St);
line({P, N, Leaf}, Path, St = #state{fixed = Fixed}) ->
  case dnf_ty_variable:smallest(P, N, Fixed) of
    {{pos, V}, _} ->
      U = ty_node:make(dnf_ty_variable:single(true, P -- [V], N, Leaf)),
      bound(upper, V, U, Path, St);
    {{neg, V}, _} ->
      L = ty_node:make(dnf_ty_variable:single(false, P, N -- [V], Leaf)),
      bound(lower, V, L, Path, St);
    {{{delta, _}, _}, _} ->
      % only monomorphic variables: they are eliminated (Part 1, Lemma C.3/C.11)
      constructors_empty(Leaf, Path, St)
  end.

% alpha <= B (upper) or B <= alpha (lower), a piece depending on Path
% Tightening an existing bound creates a new empty goal on L \ U
% unless its trivial empty below or any above;
% the goal depends on the reasons of both whole sides
-spec bound(upper | lower, variable(), ty:type(), reason(), state()) -> boolean().
bound(Mode, V, B, Path, St = #state{bounds = C}) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  {CL, CU, RL, RU} = maps:get(V, C, {Empty, Any, #{}, #{}}),
  {L, U, RL1, RU1, OtherTrivial} =
    case Mode of
      upper -> {CL, ty_node:intersect(B, CU), RL, maps:merge(RU, Path), CL =:= Empty};
      lower -> {ty_node:union(B, CL), CU, maps:merge(RL, Path), RU, CU =:= Any}
    end,
  St1 = St#state{bounds = C#{V => {L, U, RL1, RU1}}},
  case {L, U} of
    {CL, CU} when is_map_key(V, C) -> continue(St); % implied; a fresh variable still records its bound
    _ when OtherTrivial -> continue(St1);
    _ -> empty(ty_node:difference(L, U), maps:merge(RL1, RU1), St1)
  end.


% A variable-free line is decomposed
-type tuple_dnf_line() :: {[ty_tuple:type()], [ty_tuple:type()], ty_bool:type()}.
-type function_dnf_line() :: {[ty_function:type()], [ty_function:type()], ty_bool:type()}.
-type map_dnf_line() :: {[ty_map:type()], [ty_map:type()], ty_bool:type()}.
-spec constructors_empty(ty_rec:type(), reason(), state()) -> boolean().
constructors_empty(any, Path, St) -> backtrack(Path, St);
constructors_empty(empty, _Path, St) -> continue(St);
constructors_empty(TyRec, Path, St) ->
  case basic_empty(TyRec) of
    false -> backtrack(Path, St);
    true ->
      {TupDefault, TupArities} = ty_rec:pi(TyRec, ty_tuples),
      {FunDefault, FunArities} = ty_rec:pi(TyRec, ty_functions),
      Components =
        [{tuple_line, L} || L <- dnf_ty_list:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_list))] ++
        [{tuple_line, L} || L <- dnf_ty_bitstring:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_bitstring))] ++
        [{tuple_line, L} || {_Arity, D} <- lists:sort(maps:to_list(TupArities)), L <- dnf_ty_tuple:minimize_dnf(D)] ++
        [{tuple_line, L} || L <- dnf_ty_tuple:minimize_dnf(TupDefault)] ++
        [{fun_line, L} || {_Arity, D} <- lists:sort(maps:to_list(FunArities)), L <- dnf_ty_function:minimize_dnf(D)] ++
        [{fun_line, L} || L <- dnf_ty_function:minimize_dnf(FunDefault)] ++
        [{map_line, L} || L <- dnf_ty_map:minimize_dnf(ty_rec:pi(TyRec, dnf_ty_map))],
      all_of(Components, Path, St)
  end.

-spec basic_empty(ty_rec:type_record()) -> boolean().
basic_empty(TyRec) ->
  element(1, dnf_ty_predefined:is_empty(ty_rec:pi(TyRec, dnf_ty_predefined), #{}))
    andalso element(1, dnf_ty_atom:is_empty(ty_rec:pi(TyRec, dnf_ty_atom), #{}))
    andalso element(1, dnf_ty_interval:is_empty(ty_rec:pi(TyRec, dnf_ty_interval), #{})).

-spec tuple_line(tuple_dnf_line(), reason(), state()) -> boolean().
tuple_line({[], [], _}, Path, St) -> backtrack(Path, St); % the whole product: never empty
tuple_line({[], Neg = [TNeg | _], Leaf}, Path, St) ->
  Dim = length(ty_tuple:components(TNeg)),
  tuple_line({[ty_tuple:any(Dim)], Neg, Leaf}, Path, St);
tuple_line({Pos, Neg, _}, Path, St) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, Path, St).

-spec map_line(map_dnf_line(), reason(), state()) -> boolean().
map_line({[], [], _}, Path, St) -> backtrack(Path, St);
map_line({[], Neg = [_ | _], Leaf}, Path, St) ->
  P1 = ty:tuples(ty_tuples:singleton(2, dnf_ty_tuple:any())),
  P2 = ty:functions(ty_functions:singleton(2, dnf_ty_function:any())),
  map_line({[ty_map:map(P1, P2)], Neg, Leaf}, Path, St);
map_line({Pos, Neg, _}, Path, St) ->
  phi(ty_tuple:components(ty_tuple:big_intersect(Pos)), Neg, Path, St).

-spec phi([ty:type()], [ty_tuple:type()], reason(), state()) -> boolean().
phi(BigS, Neg, Path, St) ->
  Components = [{empty, S} || S <- BigS],
  Alternatives = case Neg of
    [] -> Components;
    [Ty | N] -> Components ++ [{all, without(BigS, ty_tuple:components(Ty), 1, N)}]
  end,
  any_of(Alternatives, Path, St).

-spec without([ty:type()], [ty:type()], pos_integer(), [ty_tuple:type()]) -> [goal()].
without(_BigS, [], _I, _N) -> [];
without(BigS, [NComp | Rest], I, N) ->
  [{phi_tuple, replace_at(I, BigS, NComp), N} | without(BigS, Rest, I + 1, N)].

-spec replace_at(pos_integer(), [ty:type()], ty:type()) -> [ty:type()].
replace_at(1, [H | T], NComp) -> [ty_node:difference(H, NComp) | T];
replace_at(I, [H | T], NComp) -> [H | replace_at(I - 1, T, NComp)].

-spec function_line(function_dnf_line(), reason(), state()) -> boolean().
function_line({Pos, Neg, _}, Path, St) ->
  S = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotS = ty_node:negate(S),
  Alternatives =
    [{all, [{empty, ty_node:intersect(ty_function:domain(F), NotS)},
            {fun_explore, ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos}]}
     || F <- Neg],
  any_of(Alternatives, Path, St).

-spec explore(ty:type(), ty:type(), [ty_function:type()], reason(), state()) -> boolean().
explore(T1, T2, [], Path, St) ->
  any_of([{empty, T1}, {empty, T2}], Path, St);
explore(T1, T2, [F | Ps], Path, St) ->
  S1 = ty_function:domain(F),
  S2 = ty_function:codomain(F),
  any_of([{empty, T1},
          {empty, T2},
          {all, [{fun_explore, T1, ty_node:intersect(T2, S2), Ps},
                 {fun_explore, ty_node:difference(T1, S1), T2, Ps}]}],
         Path, St).
