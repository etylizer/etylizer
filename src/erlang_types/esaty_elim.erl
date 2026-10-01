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
-include("etylizer.hrl").

-type ty() :: ty_node:type().
-type polarity() :: pos | neg.
-type occurrence() :: polarity() | both.
-type occurrences() :: #{variable() => occurrence()}.

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
            case body(maps:get(V, Occs, none), L, U) of
                keep -> Acc;
                {take, Body} ->
                    Mentioned = sets:to_list(sets:union(ty_node:all_variables(L), ty_node:all_variables(U))),
                    Keep = lists:member(V, Mentioned) orelse sets:is_element(V, Taken)
                        orelse lists:any(fun(W) -> is_map_key(W, S) end, Mentioned),
                    case Keep of
                        true -> Acc;
                        false ->
                            ?METRIC_COUNT(eliminate, variable),
                            {S#{V => Body}, sets:union(Taken, ty_node:all_variables(Body))}
                    end
            end
        end, {#{}, sets:new()}, Candidates),
    check(Sigma, Occs, Roots),
    Sigma.

% The bound a variable takes: the lower one if everything grows with it (or
% it occurs nowhere), the upper one if everything shrinks, none if it occurs
% at both polarities.
-spec body(occurrence() | none, ty(), ty()) -> {take, ty()} | keep.
body(pos, L, _U) -> {take, L};
body(neg, _L, U) -> {take, U};
body(none, L, _U) -> {take, L};
body(both, _L, _U) -> keep.

% The polarities at which the variables occur in the given types: a variable
% is pos if every type taken at pos grows with it and every type taken at neg
% shrinks. Follows the representation: a node is a BDD over variables, its
% leaves are BDDs over nominal tags, their leaves are type records, a record
% holds BDDs over tuple and arrow atoms, and the atoms hold nodes. The
% negative edge of a BDD node and the domains of an arrow flip the polarity.
-type acc() :: {#{{ty(), polarity()} => []}, occurrences()}.

-spec polarities([{ty(), polarity()}]) -> occurrences().
polarities(Roots) ->
    {_, Occs} = lists:foldl(fun({T, P}, Acc) -> node(T, P, Acc) end, {#{}, #{}}, Roots),
    Occs.

-spec node(ty(), polarity(), acc()) -> acc().
node(T, P, Acc = {Visited, Occs}) ->
    case Visited of
        #{{T, P} := _} -> Acc;
        _ -> variables(ty_node:load(T), P, {Visited#{{T, P} => []}, Occs})
    end.

% The polarities the atom of a BDD node occurs at, the node taken at P. The
% node is (Atom /\ Pos) \/ (not Atom /\ Neg): without the atom's negation if
% Neg is empty, and equal to Atom \/ Neg if Pos is everything.
-spec atom_at(B, B, B, B, polarity()) -> [polarity()].
atom_at(Pos, Neg, Empty, Any, P) ->
    [P || Pos =/= Empty, Neg =/= Any] ++ [flip(P) || Neg =/= Empty, Pos =/= Any].

% a BDD over variables; its leaves are BDDs over nominal tags
-spec variables(dnf_ty_variable:type(), polarity(), acc()) -> acc().
variables({leaf, Nominal}, P, Acc) -> nominals(Nominal, P, Acc);
variables({node, V, Pos, Neg}, P, {Visited, Occs}) ->
    At = atom_at(Pos, Neg, dnf_ty_variable:empty(), dnf_ty_variable:any(), P),
    Occs1 = lists:foldl(fun(Q, O) -> occurs(V, Q, O) end, Occs, At),
    variables(Neg, P, variables(Pos, P, {Visited, Occs1})).

-spec occurs(variable(), polarity(), occurrences()) -> occurrences().
occurs(V, P, Occs) ->
    maps:update_with(V, fun(P0) when P0 =:= P -> P; (_) -> both end, P, Occs).

% a BDD over nominal tags; a tag holds no variable, the leaves are type records
-spec nominals(dnf_ty_nominal:type(), polarity(), acc()) -> acc().
nominals({leaf, Rec}, P, Acc) -> record(Rec, P, Acc);
nominals({node, _Tag, Pos, Neg}, P, Acc) -> nominals(Neg, P, nominals(Pos, P, Acc)).

-spec record(ty_rec:type(), polarity(), acc()) -> acc().
record(any, _P, Acc) -> Acc;
record(empty, _P, Acc) -> Acc;
record(Rec, P, Acc) ->
    {TupleDefault, Tuples} = ty_rec:pi(Rec, ty_tuples),
    {FunDefault, Funs} = ty_rec:pi(Rec, ty_functions),
    Bdds = [ty_rec:pi(Rec, dnf_ty_list), ty_rec:pi(Rec, dnf_ty_bitstring), ty_rec:pi(Rec, dnf_ty_map),
            TupleDefault, FunDefault | maps:values(Tuples) ++ maps:values(Funs)],
    lists:foldl(fun(B, A) -> constructors(B, P, A) end, Acc, Bdds).

% a BDD over tuples (lists, bitstrings and maps are tuples too) or arrows;
% its leaves are booleans
-type constructor_bdd() :: dnf_ty_tuple:type() | dnf_ty_function:type().

-spec constructors(constructor_bdd(), polarity(), acc()) -> acc().
constructors({leaf, _}, _P, Acc) -> Acc;
constructors({node, Atom, Pos, Neg}, P, Acc) ->
    Acc1 = lists:foldl(fun(Q, A) -> atom(Atom, Q, A) end, Acc, atom_at(Pos, Neg, {leaf, 0}, {leaf, 1}, P)),
    constructors(Neg, P, constructors(Pos, P, Acc1)).

-spec atom(ty_tuple:type() | ty_function:type(), polarity(), acc()) -> acc().
atom({ty_function, Domains, Codomain}, P, Acc) ->
    node(Codomain, P, lists:foldl(fun(D, A) -> node(D, flip(P), A) end, Acc, Domains));
atom({ty_tuple, _, Refs}, P, Acc) ->
    lists:foldl(fun(R, A) -> node(R, P, A) end, Acc, Refs).

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
                     true -> ?assert_pattern(true, ty_node:leq(T1, T));
                     false -> ?assert_pattern(true, ty_node:leq(T, T1))
                 end
             end || V <- maps:keys(Sigma), Occ <- [maps:get(V, Occs, none)], Occ =/= none, {T, P} <- Roots,
                    sets:is_element(V, ty_node:all_variables(T))],
            ok
    end.
