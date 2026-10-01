-module(esaty_elim).

% Variable elimination for SaTy (esaty:is_satisfiable_elim/2).
%
% Between two input constraints the search holds bounds `L <: V <: U` for the
% variables met so far and has the remaining inputs still to run. Every one of
% these is a type D that has to be empty: an input `A <: B` is `A \ B`, a bound
% is `L \ V` and `V \ U`. If every D is increasing in a variable V, the subject
% of V's own bounds aside, then whatever solves the constraints with a type
% for V solves them with a smaller one, so V may take its lower bound L, and
% `L <: U` is all its own bounds still ask for. If every D is decreasing, V
% takes its upper bound. V then occurs nowhere and is gone.
%
% This preserves satisfiability, not the set of solutions.

-export([sigma/3]).

-include("constraints.hrl").
-include("metrics.hrl").

-type ty() :: ty_node:type().
-type polarity() :: pos | neg.

% The variables to eliminate, with the type each one takes. Roots are the
% types the variables may still occur in, a type at pos if it has to shrink
% (the left side of an input, a lower bound) and at neg if it has to grow.
% The variables of one round do not occur in each other's bounds.
-spec sigma([{ty(), polarity()}], #{variable() => {ty(), ty()}}, monomorphic_variables()) -> #{variable() => ty()}.
sigma(Roots, Bounds, Fixed) ->
    Occs = polarities(Roots),
    Candidates = lists:sort(fun ty_variable:leq/2,
        [V || V <- lists:usort(maps:keys(Bounds) ++ maps:keys(Occs)),
              not is_map_key(V, Fixed), element(1, ty_variable:is_frame(V)) =:= false]),
    {Sigma, _} = lists:foldl(
        fun(V, Acc = {S, Taken}) ->
            {L, U} = maps:get(V, Bounds, {ty_node:empty(), ty_node:any()}),
            Body = case maps:get(V, Occs, none) of pos -> L; neg -> U; none -> L; both -> keep end,
            Mentioned = sets:to_list(sets:union(ty_node:all_variables(L), ty_node:all_variables(U))),
            Keep = Body =:= keep orelse lists:member(V, Mentioned) orelse sets:is_element(V, Taken)
                orelse lists:any(fun(W) -> is_map_key(W, S) end, Mentioned),
            case Keep of
                true -> Acc;
                false ->
                    ?METRIC_COUNT(eliminate, variable),
                    {S#{V => Body}, sets:union(Taken, ty_node:all_variables(Body))}
            end
        end, {#{}, sets:new()}, Candidates),
    check(Sigma, Occs, Roots),
    Sigma.

% The polarities at which the variables occur in the given types: a variable
% is pos if every type taken at pos grows with it and every type taken at neg
% shrinks. Follows the representation: a node is a BDD over variables with
% type records as leaves, a record holds BDDs over tuple and arrow atoms, and
% the atoms hold nodes. The negative edge of a BDD node and the domains of an
% arrow flip the polarity.
-type acc() :: {#{{ty(), polarity()} => []}, #{variable() => polarity() | both}}.

-spec polarities([{ty(), polarity()}]) -> #{variable() => polarity() | both}.
polarities(Roots) ->
    {_, Occs} = lists:foldl(fun({T, P}, Acc) -> node(T, P, Acc) end, {#{}, #{}}, Roots),
    Occs.

-spec node(ty(), polarity(), acc()) -> acc().
node(T, P, Acc = {Visited, Occs}) ->
    case Visited of
        #{{T, P} := _} -> Acc;
        _ -> bdd(ty_node:load(T), P, {Visited#{{T, P} => []}, Occs})
    end.

% a BDD over variables, tuples or arrows
-spec bdd(term(), polarity(), acc()) -> acc().
bdd({leaf, Leaf}, P, Acc) -> leaf(Leaf, P, Acc);
bdd({node, Atom, Pos, Neg}, P, Acc) ->
    % (Atom /\ Pos) \/ (not Atom /\ Neg): without the atom's negation if Neg
    % is empty, and equal to Atom \/ Neg if Pos is everything
    Acc1 = case empty_leaf(Pos) orelse any_leaf(Neg) of true -> Acc; false -> atom(Atom, P, Acc) end,
    Acc2 = case empty_leaf(Neg) orelse any_leaf(Pos) of true -> Acc1; false -> atom(Atom, flip(P), Acc1) end,
    bdd(Neg, P, bdd(Pos, P, Acc2)).

% the leaf of a variable BDD is a type record, that of the others a boolean
-spec leaf(term(), polarity(), acc()) -> acc().
leaf(Leaf, _P, Acc) when Leaf =:= any; Leaf =:= empty; Leaf =:= 0; Leaf =:= 1 -> Acc;
leaf(Rec, P, Acc) ->
    {TupleDefault, Tuples} = ty_rec:pi(Rec, ty_tuples),
    {FunDefault, Funs} = ty_rec:pi(Rec, ty_functions),
    Bdds = [ty_rec:pi(Rec, dnf_ty_list), ty_rec:pi(Rec, dnf_ty_bitstring), ty_rec:pi(Rec, dnf_ty_map),
            TupleDefault, FunDefault | maps:values(Tuples) ++ maps:values(Funs)],
    lists:foldl(fun(B, A) -> bdd(B, P, A) end, Acc, Bdds).

-spec atom(term(), polarity(), acc()) -> acc().
atom({ty_function, Domains, Codomain}, P, Acc) ->
    node(Codomain, P, lists:foldl(fun(D, A) -> node(D, flip(P), A) end, Acc, Domains));
atom({ty_tuple, _, Refs}, P, Acc) ->
    lists:foldl(fun(R, A) -> node(R, P, A) end, Acc, Refs);
atom(V, P, {Visited, Occs}) ->
    {Visited, maps:update_with(V, fun(P0) when P0 =:= P -> P; (_) -> both end, P, Occs)}.

-spec empty_leaf(term()) -> boolean().
empty_leaf({leaf, empty}) -> true;
empty_leaf({leaf, 0}) -> true;
empty_leaf(_) -> false.

-spec any_leaf(term()) -> boolean().
any_leaf({leaf, any}) -> true;
any_leaf({leaf, 1}) -> true;
any_leaf(_) -> false.

-spec flip(polarity()) -> polarity().
flip(pos) -> neg;
flip(neg) -> pos.

% With ESATY_ELIM_CHECK set, the polarities read off the representation are
% checked semantically: T grows with V exactly if T[V := V /\ G] <: T for a
% fresh G.
-spec check(#{variable() => ty()}, #{variable() => polarity() | both}, [{ty(), polarity()}]) -> ok.
check(Sigma, Occs, Roots) ->
    case map_size(Sigma) > 0 andalso os:getenv("ESATY_ELIM_CHECK") of
        false -> ok;
        _ ->
            Var = fun(V) -> ty_node:make(dnf_ty_variable:singleton(V)) end,
            G = Var(ty_variable:new_with_name('$esaty_elim_check')),
            [begin
                 T1 = ty_node:substitute(T, #{V => ty_node:intersect(Var(V), G)}),
                 case (Occ =:= pos) =:= (P =:= pos) of
                     true -> true = ty_node:leq(T1, T);
                     false -> true = ty_node:leq(T, T1)
                 end
             end || V <- maps:keys(Sigma), Occ <- [maps:get(V, Occs, none)], Occ =/= none, {T, P} <- Roots,
                    sets:is_element(V, ty_node:all_variables(T))],
            ok
    end.
