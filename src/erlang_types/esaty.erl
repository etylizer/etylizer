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
%% into C on the spot. A variable's bounds are kept as the pieces that were
%% merged into them; a new piece is checked against every piece on the
%% other side, since
%% (L1 | L2) \ (U1 & U2) = L1 \ U1 | L1 \ U2 | L2 \ U1 | L2 \ U2, and each
%% pair is an empty goal run right away: the consequence that saturation
%% would add later, one piece pair at a time. The search succeeds when
%% Pending is exhausted: every line consumed, every consequence established,
%% C saturated by construction. It fails when the choice stack is: every
%% alternative refuted. The correspondence with a SAT solver:
%%
%%   partial assignment      the bound map C : variable -> {Lower, Upper}
%%   literal                 one one-sided bound from the NTLV rule
%%   decision                an OR of the tuple or function decomposition
%%   theory propagation      the consequence goal of a new piece pair
%%   conflict                a line that cannot be made empty under C
%%   conflict analysis       the reason set of a failure: the decisions the
%%                           pieces it read depend on
%%   backjumping             a decision that a failure does not depend on
%%                           does not try its other alternatives
%%   learning                a goal that failed on its own, under the pieces
%%                           it read, fails at once wherever those pieces
%%                           are present
%%   model                   Pending exhausted
%%
%% The engine. Goals are data, and the search is three mutually
%% tail-recursive functions, so it runs in constant Erlang stack however
%% deep the path:
%%
%%   goal/3      runs a goal under the current state and path
%%   continue/1  the goal succeeded: the next goal on Pending runs -- the
%%               remaining conjuncts of an enclosing conjunction, the exit of
%%               an enclosing activation, the key of an enclosing phi_tuple
%%               or fun_explore goal to add to X
%%   backtrack/2 the goal failed: the choice stack is unwound, every handler
%%               seeing the failure in turn -- the tag of every activation
%%               whose continuation ran, the nogood of every activation that
%%               failed on its own -- until a decision the failure depends on
%%               has an alternative left
%%
%% Pending is what is left to do when a goal succeeds, and the choice stack
%% is what a failure returns through: a decision for every OR on the path,
%% and every activation started or exited on it. A decision keeps the state
%% and Pending it was made under, so its next alternative starts from them.
%% Pending has to be kept and cannot be read off a single stack shared with
%% the decisions: for A = A1 | A2 followed by B, the decision for A2 is
%% pushed above B, A1 succeeds and B is popped, B fails, and the alternative
%% A2 has to run B again, which is gone from Pending. Pending is a list
%% shared by every alternative, so keeping it costs one word.
%%
%% Reasons. Every piece carries the decisions it depends on (the decisions
%% above the line that emitted it), a consequence goal inherits the reasons
%% of the two pieces it relates, a ground line that cannot be made empty
%% fails with the reasons of its goal, and a decision whose alternative
%% fails for a reason it is not part of fails with that reason at once: no
%% piece the decision produced was read by the failure, so the same failure
%% exists under every alternative.
%%
%% Learning. Every activation of empty(T) records the pieces it reads, a
%% failure carries the reads that led to it, and a tag on the choice stack,
%% pushed when the activation exits, tells a local failure from one of the
%% rest of the search. When an activation fails without ever having exited, T
%% could not be made empty by itself given the pieces it read that existed
%% before it started (its own pieces it would make again): {T, those pieces}
%% is a nogood. Everything a search does depends on C only through the
%% pieces its consequences pair up, so the nogood holds wherever those
%% pieces are present, and a hit fails with exactly their current reasons
%% plus the path of the goal. Pieces are numbered by an epoch on the path to
%% tell an activation's own pieces from the ones it found. The store travels
%% in the search state and comes back in failures, so what a failed branch
%% learned is known to every later one.
%%
%% The coinductive hypotheses of the emptiness algorithm and the goals
%% already achieved on the current path live in X, threaded in the search
%% state along Pending: a recursive type met again is assumed empty, and a
%% sub-goal met again on the same path is skipped since its bounds are
%% already in C. Backtracking discards X, the epoch and the reads with the
%% path.
%%
%% SaTy searches exactly the tree normalize + saturate materialize:
%% the same minimized lines, the same singled bounds, the same
%% decompositions, with prunings that lose no answer. A goal achieved on the
%% path is not redone (C already lies inside it, the other alternatives only
%% tighten C, and any path below a tighter set has a solution that also
%% satisfies C and the pending goals). Skipping an achieved or in-progress
%% goal, or a consequence already implied, only weakens a search, so a
%% failure found with skips holds without them, and a failure under fewer
%% pieces holds under more.

-export([is_satisfiable/2]).

-include("constraints.hrl").

% data structure used for caching
-type memo_set(A) :: #{A => []}.

% problem input shape
-type input_constraints() :: [{ty:type(), ty:type()}].

% the decisions a piece, a goal or a failure depends on
-type reason() :: #{integer() => []}.

% pieces are numbered in the order they are made on the path
-type epoch() :: non_neg_integer().

% one bound emitted for a variable: the node, the decisions it depends on,
% and its epoch
-type piece() :: {ty:type(), reason(), epoch()}.

% the current bounds of every variable constrained so far,
% merged and as pieces: the lower bound is the union of the lower pieces,
% the upper bound the intersection of the upper pieces
% if the inputs constraints are satisfiable,
% these bounds denote one valid substitution (pre-solved) substitution
-type bounds() :: #{variable() => {ty:type(), ty:type(), [piece()], [piece()]}}.

% the cache for the coinductive hypothesis,
% is modified when empty(T) starts
% and when a phi_tuple or fun_explore goal completes
-type cache() :: memo_set({node, ty:type()} | cached_goal()).
-type cached_goal() :: {phi_tuple, [ty:type()], [ty_tuple:type()]}
                     | {fun_explore, ty:type(), ty:type(), [ty_function:type()]}.

% the pieces an activation has read, with their epochs
-type read() :: {variable(), lower | upper, ty:type()}.
-type reads() :: #{read() => epoch()}.

% nogoods: the read sets under which empty(T) failed on its own
-type store() :: #{ty:type() => [reads()]}.

% conjunction of goals
-type conjuncts() :: [goal()].

% A search goal
-type goal() :: 
    {empty, ty:type()} % make the node empty
  | {consequence, ty:type(), reason(), read(), epoch()} % a piece pair, reading one of them
  | {line, {[variable()], [variable()], ty_rec:type()}} % a DNF line of a node
  | {all, conjuncts()} % a conjunction of goals; disjunctions are not part of goals
  % decomposition of tuples
  | {tuple_line, tuple_dnf_line()}
  | {phi_tuple, [ty:type()], [ty_tuple:type()]}
  % decomposition of functions
  | {fun_line, function_dnf_line()}
  | {fun_explore, ty:type(), ty:type(), [ty_function:type()]}
  % decomposition of maps
  | {map_line, map_dnf_line()}
  % bookkeeping
  | {exit, reads(), integer()} % leave an activation: its reads, its token
  | {achieve, cached_goal()}. % a phi_tuple or fun_explore goal completed

% pending is the rest of the search after a goal succeeds,
% each goal with the decisions it depends on
-type pending() :: [{goal(), reason()}].

% what a failure meets on its way back, innermost first:
% disjunctions are the decisions to backtrack to
-type choice() :: {decide, untried_alternatives(), state(), reason(), integer(), reason(), reads()} % a decision: its untried alternatives and state
                 | {tag, integer()}                                   % an activation exited: its continuation failed
                 | {activation, ty:type(), integer(), epoch(), reads()}. % an activation started: learn its nogood
-type untried_alternatives() :: [goal()]. % can be empty
-type choices() :: [choice()].

-define(NOGOODS_PER_NODE, 32).

-record(state, {
  % immutable, set once at the beginning, not used for bounds()
  fixed :: monomorphic_variables(),
  % bounds of all poly variables which get refined 
  % until either a conflict occurs and the search backtracks to the latest decision it depends on (restoring bounds),
  % or all goals succeed and the refined bounds can be used to compute a valid (i.e. saturated) substitution
  bounds :: bounds(),
  % cache used for coinductive hypothesis and completed goals
  cache :: cache(),
  % the epoch of the next piece made on the path
  epoch :: epoch(),
  % the pieces the current activation has read
  reads :: reads(),
  % the nogoods learned so far, kept when backtracking
  store :: store(),
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
  St = #state{fixed = Fixed, bounds = #{}, cache = #{}, epoch = 0, reads = #{}, store = #{}, pending = [{{all, Goals}, #{}}], choices = []},
  continue(St).

% run one goal under the decisions its existence depends on
-spec goal(goal(), reason(), state()) -> boolean().
goal(Goal, Path, St) ->
  case Goal of
    {empty, T} -> empty(T, Path, St);
    {consequence, T, PairPath, Read, Epoch} ->
      #state{reads = Reads} = St,
      empty(T, PairPath, St#state{reads = Reads#{Read => Epoch}});
    {line, L} -> line(L, Path, St);
    {all, Goals} -> all_of(Goals, Path, St);
    {tuple_line, L} -> tuple_line(L, Path, St);
    {phi_tuple, BigS, Neg} -> phi(BigS, Neg, Path, St);
    {fun_line, L} -> function_line(L, Path, St);
    {fun_explore, T1, T2, P} -> explore(T1, T2, P, Path, St);
    {map_line, L} -> map_line(L, Path, St);
    {exit, Reads0, Tok} ->
      % the activation hands its reads on; from here on a failure is one of
      % the rest of the search, which the tag tells its activation
      #state{reads = ReadsIn, choices = Ch} = St,
      continue(St#state{reads = maps:merge(Reads0, ReadsIn), choices = [{tag, Tok} | Ch]});
    {achieve, Key} ->
      #state{cache = Cache} = St,
      continue(St#state{cache = Cache#{Key => []}})
  end.

% run the next pending goal under the decisions it depends on
% if there are no pending goals, the search has succeeded
-spec continue(state()) -> boolean().
continue(#state{pending = []}) -> true;
continue(St = #state{pending = [{G, Path} | Pending]}) ->
  goal(G, Path, St#state{pending = Pending}).

% when there is a conflict for reason R, having read the reads of the state,
% with what was learned in its store:
% every handler on the choice stack sees the conflict in turn,
% until a decision R depends on has an alternative left.
% if there is none, the constraints are unsatisfiable.
-spec backtrack(reason(), state()) -> boolean().
backtrack(_R, #state{choices = []}) -> false;
backtrack(R, St = #state{reads = Reads, store = Store, choices = [{decide, UntriedAlternatives, Saved, Path, D, Acc, ReadsAcc} | Ch]}) ->
  case R of
    #{D := _} ->
      decide(UntriedAlternatives, Path, D, maps:merge(Acc, R), maps:merge(ReadsAcc, Reads), Saved#state{store = Store});
    _ ->
      backtrack(R, St#state{choices = Ch})
  end;
backtrack(R, St = #state{choices = [{tag, Tok} | Ch]}) ->
  backtrack(R#{Tok => []}, St#state{choices = Ch});
backtrack(R, St = #state{reads = ReadsIn, store = Store, choices = [{activation, T, Tok, E0, Reads0} | Ch]}) ->
  case R of
    #{Tok := _} ->
      backtrack(maps:remove(Tok, R), St#state{choices = Ch});
    _ ->
      Found = maps:filter(fun(_, E) -> E < E0 end, ReadsIn),
      backtrack(R, St#state{reads = maps:merge(Reads0, ReadsIn), store = learn(T, Found, Store), choices = Ch})
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
% with the current state in the decision (for failure)
% an empty disjunction is a conflict
% an alternative that fails for a reason this decision is not part of fails
% the decision at once, since the same failure exists under every other
% alternative; otherwise the next alternative is tried with what the failed
% one learned, and the reasons and reads of all of them are the reason the
% decision fails
-spec any_of(untried_alternatives(), reason(), state()) -> boolean().
any_of([], Path, St) -> backtrack(Path, St);
any_of(Goals, Path, St = #state{reads = Reads}) ->
  D = erlang:unique_integer([positive]),
  decide(Goals, Path, D, #{}, Reads, St).

% a decision keeps the state it was made under, whose choices are the ones
% below it
-spec decide(untried_alternatives(), reason(), integer(), reason(), reads(), state()) -> boolean().
decide([], _Path, D, Acc, Reads, St) ->
  backtrack(maps:remove(D, Acc), St#state{reads = Reads});
decide([G | Gs], Path, D, Acc, Reads, St = #state{choices = Ch}) ->
  goal(G, Path#{D => []}, St#state{choices = [{decide, Gs, St, Path, D, Acc, Reads} | Ch]}).

% make type T empty
% one activation: it reads into a fresh read set, hands its reads on when it
% exits, and if it fails before it ever exited, {T, the pieces it read that
% predate it} is learned
-spec empty(ty:type(), reason(), state()) -> boolean().
empty(T, Path, St = #state{fixed = Fixed, bounds = C, cache = Cache, epoch = E0, reads = Reads0, store = Store0, pending = Pending, choices = Ch}) ->
  case Cache of
    #{{node, T} := _} -> continue(St);
    _ ->
      case known_failure(T, C, Store0) of
        {true, Reads, Reason} ->
          backtrack(maps:merge(Path, Reason), St#state{reads = maps:merge(Reads0, Reads)});
        false ->
          Tok = erlang:unique_integer([positive]),
          Lines = ground_first(dnf_ty_variable:minimize_dnf(ty_node:load(T)), Fixed),
          all_of([{line, L} || L <- Lines], Path,
                 St#state{cache = Cache#{{node, T} => []}, reads = #{},
                          pending = [{{exit, Reads0, Tok}, Path} | Pending], choices = [{activation, T, Tok, E0, Reads0} | Ch]})
      end
  end.

%% Lines without a polymorphic variable go first: they are the only ones that
%% can fail on their own, and a variable line only emits a bound.
-spec ground_first([L], monomorphic_variables()) -> [L] when L :: {[variable()], [variable()], ty_rec:type()}.
ground_first(Lines, Fixed) ->
  {Ground, Poly} = lists:partition(
    fun({P, N, _}) -> lists:all(fun(V) -> maps:is_key(V, Fixed) end, P ++ N) end, Lines),
  Ground ++ Poly.

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
% a piece the current bound already implies changes nothing;
% otherwise the new piece must fit every piece on the other side:
% one consequence per pair, each reading the other piece
-spec bound(upper | lower, variable(), ty:type(), reason(), state()) -> boolean().
bound(Mode, V, B, Path, St = #state{bounds = C, epoch = E}) ->
  Empty = ty_node:empty(),
  Any = ty_node:any(),
  {CL, CU, Ls, Us} = maps:get(V, C, {Empty, Any, [], []}),
  Piece = {B, Path, E},
  {L, U, Ls1, Us1, Others} =
    case Mode of
      upper -> {CL, intersect_bound(B, CU), Ls, [Piece | Us], Ls};
      lower -> {union_bound(B, CL), CU, [Piece | Ls], Us, Us}
    end,
  St1 = St#state{bounds = C#{V => {L, U, Ls1, Us1}}, epoch = E + 1},
  case {L, U} of
    {CL, CU} when is_map_key(V, C) -> continue(St); % implied; a fresh variable still records its piece
    _ -> consequences([pair(Mode, V, Piece, Other) || Other <- Others], St1)
  end.

% a new piece against a piece on the other side: lower <= upper,
% under both pieces' reasons, reading the other piece
-spec pair(upper | lower, variable(), piece(), piece()) -> {ty:type(), reason(), read(), epoch()}.
pair(upper, V, {U, Path, _}, {L, RL, EL}) -> {ty_node:difference(L, U), maps:merge(RL, Path), {V, lower, L}, EL};
pair(lower, V, {L, Path, _}, {U, RU, EU}) -> {ty_node:difference(L, U), maps:merge(RU, Path), {V, upper, U}, EU}.

%% The consequences of a new piece: for every piece on the other side, the
%% pair must satisfy lower <= upper. Each is an empty goal under the two
%% pieces' reasons, and reads the piece it was paired with.
-spec consequences([{ty:type(), reason(), read(), epoch()}], state()) -> boolean().
consequences(Pairs, St) ->
  all_of([{consequence, T, Path, Read, Epoch} || {T, Path, Read, Epoch} <- Pairs], #{}, St).

-spec learn(ty:type(), reads(), store()) -> store().
learn(T, Reads, Store) ->
  Known = maps:get(T, Store, []),
  Store#{T => lists:sublist([Reads | Known], ?NOGOODS_PER_NODE)}.

%% A nogood applies when every piece it read is present. Its reads come back
%% with the pieces' current epochs, and its reason is the pieces' current
%% reasons.
-spec known_failure(ty:type(), bounds(), store()) -> false | {true, reads(), reason()}.
known_failure(T, C, Store) ->
  case Store of
    #{T := Known} -> match_nogoods(Known, C);
    _ -> false
  end.

-spec match_nogoods([reads()], bounds()) -> false | {true, reads(), reason()}.
match_nogoods([], _C) -> false;
match_nogoods([Reads | Rest], C) ->
  case present(maps:keys(Reads), C, #{}, #{}) of
    {true, Current, Reason} -> {true, Current, Reason};
    false -> match_nogoods(Rest, C)
  end.

-spec present([read()], bounds(), reads(), reason()) -> false | {true, reads(), reason()}.
present([], _C, Current, Reason) -> {true, Current, Reason};
present([Read = {V, Side, Node} | Rest], C, Current, Reason) ->
  case C of
    #{V := {_, _, Ls, Us}} ->
      Pieces = case Side of lower -> Ls; upper -> Us end,
      case lists:keyfind(Node, 1, Pieces) of
        {Node, R, E} -> present(Rest, C, Current#{Read => E}, maps:merge(Reason, R));
        false -> false
      end;
    _ -> false
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
phi(BigS, Neg, Path, St = #state{cache = Cache, pending = Pending}) ->
  Key = {phi_tuple, BigS, Neg},
  case Cache of
    #{Key := _} -> continue(St);
    _ ->
      case lists:any(fun(Si) -> maps:is_key({node, Si}, Cache) end, BigS) of
        true -> continue(St#state{cache = Cache#{Key => []}});
        false ->
          Components = [{empty, Si} || Si <- BigS],
          Alternatives = case Neg of
            [] -> Components;
            [Ty | N] -> Components ++ [{all, without(BigS, ty_tuple:components(Ty), 1, N)}]
          end,
          any_of(Alternatives, Path, St#state{pending = [{{achieve, Key}, Path} | Pending]})
      end
  end.

-spec without([ty:type()], [ty:type()], pos_integer(), [ty_tuple:type()]) -> [goal()].
without(_BigS, [], _I, _N) -> [];
without(BigS, [NComp | Rest], I, N) ->
  [{phi_tuple, replace_at(I, BigS, NComp), N} | without(BigS, Rest, I + 1, N)].

-spec replace_at(pos_integer(), [ty:type()], ty:type()) -> [ty:type()].
replace_at(1, [H | T], NComp) -> [ty_node:difference(H, NComp) | T];
replace_at(I, [H | T], NComp) -> [H | replace_at(I - 1, T, NComp)].

-spec function_line(function_dnf_line(), reason(), state()) -> boolean().
function_line({Pos, Neg, _}, Path, St) ->
  Dom = ty_node:disjunction([ty_function:domain(F) || F <- Pos]),
  NotDom = ty_node:negate(Dom),
  Alternatives =
    [{all, [{empty, ty_node:intersect(ty_function:domain(F), NotDom)},
            {fun_explore, ty_function:domain(F), ty_node:negate(ty_function:codomain(F)), Pos}]}
     || F <- Neg],
  any_of(Alternatives, Path, St).

-spec explore(ty:type(), ty:type(), [ty_function:type()], reason(), state()) -> boolean().
explore(T1, T2, P, Path, St = #state{cache = Cache, pending = Pending}) ->
  Key = {fun_explore, T1, T2, P},
  case Cache of
    #{Key := _} -> continue(St);
    _ ->
      case maps:is_key({node, T1}, Cache) orelse maps:is_key({node, T2}, Cache) of
        true -> continue(St#state{cache = Cache#{Key => []}});
        false ->
          Split = case P of
            [] -> [];
            [F | Ps] ->
              S1 = ty_function:domain(F),
              S2 = ty_function:codomain(F),
              [{all, [{fun_explore, T1, ty_node:intersect(T2, S2), Ps},
                      {fun_explore, ty_node:difference(T1, S1), T2, Ps}]}]
          end,
          any_of([{empty, T1}, {empty, T2} | Split], Path, St#state{pending = [{{achieve, Key}, Path} | Pending]})
      end
  end.

% identical nodes need no engine call; the empty and any nodes are units
-spec union_bound(T, T) -> T when T :: ty:type().
union_bound(A, A) -> A;
union_bound(A, B) ->
  case ty_node:empty() of
    A -> B;
    B -> A;
    _ -> ty_node:union(A, B)
  end.

-spec intersect_bound(T, T) -> T when T :: ty:type().
intersect_bound(A, A) -> A;
intersect_bound(A, B) ->
  case ty_node:any() of
    A -> B;
    B -> A;
    _ -> ty_node:intersect(A, B)
  end.
