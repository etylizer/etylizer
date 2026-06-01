% A generic BDD parameterized over both the 'nodes and 'leafs

-export([
    reorder/1,
    assert_valid/1,
    any/0,
    empty/0,
    singleton/1,
    negated_singleton/1,
    leaf/1,
    equal/2,
    compare/2,
    negate/1,
    union/2,
    intersect/2,
    difference/2,
    dnf/1,
    minimize_dnf/1,
    is_empty/2,
    normalize/3,
    unparse/2,
    all_variables/2,
    has_negative_only_line/1
]).

-include("erlang_types.hrl").

-export_type([type/0]).

-include("etylizer.hrl").

% hide built-in Erlang node function
-compile({no_auto_import, [node/1]}).

-define(INSIDE(Mod, Exp), case ?MODULE of Mod -> Exp; _ -> ok end).

% make erlang_ls happy
-ifndef(ATOM).
-define(ATOM, ty_bool).
-endif.
-ifndef(LEAF).
-define(LEAF, ty_bool).
-endif.

-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type type() :: bdd().
-type line() :: {[?ATOM:type()], [?ATOM:type()], ?LEAF:type()}.
-type dnf() :: [line()].
-type cube() :: {[non_neg_integer()], [non_neg_integer()], [non_neg_integer()]}.
-type leaf() :: {leaf, ?LEAF:type()}.
-type bdd_node() :: {node, _Atom :: ?ATOM:type(), _PositiveEdge :: bdd(), _NegativeEdge :: bdd()}.
-type bdd() :: leaf() | bdd_node().

%% Reorders a potentially invalid BDD
%% TODO refactor, ugly
-spec reorder(X) -> X when X :: type().
reorder({leaf, Value}) -> {leaf, ?LEAF:reorder(Value)};
reorder({node, Atom, Pos, Neg}) ->
    % Recursively reorder children first
    OrderedPos = reorder(Pos),
    OrderedNeg = reorder(Neg),

    % Get the top atoms of the children (if they exist)
    PosAtom = case OrderedPos of
        {node, PA, _, _} -> PA;
        _ -> undefined
    end,
    NegAtom = case OrderedNeg of
        {node, NA, _, _} -> NA;
        _ -> undefined
    end,

    reorder_if_needed(PosAtom, NegAtom, Atom, OrderedPos, OrderedNeg).


-spec reorder_if_needed(?ATOM:type() | undefined, ?ATOM:type() | undefined, ?ATOM:type(), type(), type()) -> type().
reorder_if_needed(PosAtom, NegAtom, Atom, OrderedPos, OrderedNeg) ->
    Z = case PosAtom of
        undefined -> reorder_check_neg(NegAtom, Atom, OrderedPos, OrderedNeg);
        PA ->
            case ?ATOM:compare(Atom, PA) /= lt of
                true -> push_down(Atom, OrderedPos, OrderedNeg);
                false -> reorder_check_neg(NegAtom, Atom, OrderedPos, OrderedNeg)
            end
    end,
    assert_valid(Z),
    Z.

-spec reorder_check_neg(?ATOM:type() | undefined, ?ATOM:type(), type(), type()) -> type().
reorder_check_neg(NegAtom, Atom, OrderedPos, OrderedNeg) ->
    case NegAtom of
        undefined -> {node, Atom, OrderedPos, OrderedNeg};
        NA ->
            case ?ATOM:compare(Atom, NA) /= lt of
                true -> push_down(Atom, OrderedPos, OrderedNeg);
                false -> {node, Atom, OrderedPos, OrderedNeg}
            end
    end.

-spec push_down(?ATOM:type(), bdd(), bdd()) -> bdd().
push_down(TopAtom, Pos, Neg) ->
    union(
        intersect(singleton(TopAtom), Pos),
        intersect(negate(singleton(TopAtom)), Neg)
    ).

-spec assert_valid(bdd()) -> bdd().
assert_valid(Bdd) -> is_ordered(Bdd).

-spec is_ordered(bdd()) -> bdd().
is_ordered(Bdd = {leaf, T}) -> ?LEAF:assert_valid(T), Bdd; % also descend into leafs
is_ordered(Bdd = {node, Atom, PositiveEdge, NegativeEdge}) ->
    % check that all atoms in positive and negative edges are smaller than current atom
    check_branch(Atom, PositiveEdge),
    check_branch(Atom, NegativeEdge),
    % check the subtrees
    is_ordered(PositiveEdge),
    is_ordered(NegativeEdge),
    Bdd.

-spec check_branch(?ATOM:type(), bdd()) -> _.
check_branch(_ParentAtom, {leaf, _}) -> ok;
check_branch(ParentAtom, Bdd = {node, ChildAtom, Left, Right}) ->
    case ?ATOM:compare(ParentAtom, ChildAtom) of
        lt -> check_branch(ParentAtom, Left), check_branch(ParentAtom, Right);
        eq -> error({eq, ParentAtom, ChildAtom, Bdd}); % shouldn't have equal atoms in proper BDD
        gt -> error({gt, ParentAtom, ChildAtom, Bdd})  % order violation
    end.

-spec any() -> bdd().
any() -> {leaf, ?LEAF:any()}.

-spec empty() -> bdd().
empty() -> {leaf, ?LEAF:empty()}.

-spec singleton(?ATOM:type()) -> bdd().
singleton(Atom) -> {node, Atom, any(), empty()}.

-spec negated_singleton(?ATOM:type()) -> bdd().
negated_singleton(Atom) -> {node, Atom, empty(), any()}.

-spec leaf(?LEAF:type()) -> bdd().
leaf(Leaf) -> {leaf, Leaf}.

-spec equal(type(), type()) -> boolean().
equal({node, A1, P1, N1}, {node, A2, P2, N2}) ->
    ?ATOM:equal(A1, A2) andalso equal(P1, P2) andalso equal(N1, N2);
equal({leaf, T1}, {leaf, T2}) -> ?LEAF:equal(T1, T2);
equal(_, _) -> false.

-spec compare(bdd(), bdd()) -> lt | gt | eq.
compare({leaf, T1}, {leaf, T2}) -> ?LEAF:compare(T1, T2);
compare({leaf, _}, {node, _, _, _}) -> lt;
compare({node, _, _, _}, {leaf, _}) -> gt;
compare({node, A1, P1, N1}, {node, A2, P2, N2}) ->
    case ?ATOM:compare(A1, A2) of
        eq ->
            case compare(P1, P2) of
                eq -> compare(N1, N2);
                Res -> Res
            end;
        Res -> Res
    end.

-spec negate(bdd()) -> bdd().
negate({leaf, A}) -> {leaf, ?LEAF:negate(A)};
negate({node, Atom, Pos, Neg}) -> {node, Atom, negate(Pos), negate(Neg)}.

% simplification for BDDs
% implements a simple form of structural subsumption
% which is not apparant at first glance
% TODO example here
-spec normalize(type()) -> type().
normalize(Bdd = {node, _Atom, Pos, Neg}) ->
    case equal(Pos, Neg) of
        true -> Pos;
        false -> Bdd
    end;
normalize(X) -> X.

-spec op(fun((?LEAF:type(), ?LEAF:type()) -> ?LEAF:type()), bdd(), bdd()) -> bdd().
op(LeafOperation, T1, T2) ->
    Res =
    case {T1, T2} of
        {{leaf, L1}, {leaf, L2}} -> 
            {leaf, LeafOperation(L1, L2)};
        {{leaf, L}, {node, A, P, N}} ->
            {node, A, op(LeafOperation, {leaf, L}, P), op(LeafOperation, {leaf, L}, N)};
        {{node, A, P, N}, {leaf, L}} ->
            {node, A, op(LeafOperation, P, {leaf, L}), op(LeafOperation, N, {leaf, L})};
        {{node, A1, P1, N1}, {node, A2, P2, N2}} ->
            leaf_op_eq(LeafOperation, T1, T2, A1, P1, N1, A2, P2, N2)
    end,
    normalize(Res).

-spec leaf_op_eq(fun((?LEAF:type(), ?LEAF:type()) -> ?LEAF:type()), B, B, A, B, B, A, B, B) -> 
    B when B :: bdd(), A :: ?ATOM:type().
leaf_op_eq(LeafOperation, T1, T2, A1, P1, N1, A2, P2, N2) -> 
    case ?ATOM:compare(A1, A2) of
        lt -> {node, A1, op(LeafOperation, P1, T2), op(LeafOperation, N1, T2)};
        gt -> {node, A2, op(LeafOperation, T1, P2), op(LeafOperation, T1, N2)};
        eq -> {node, A1, op(LeafOperation, P1, P2), op(LeafOperation, N1, N2)}
    end.

-spec union(bdd(), bdd()) -> bdd().
union(T1, T2) ->
    op(fun ?LEAF:union/2, T1, T2).

-spec intersect(bdd(), bdd()) -> bdd().
intersect(T1, T2) ->
    op(fun ?LEAF:intersect/2, T1, T2).

-spec difference(bdd(), bdd()) -> bdd().
difference(T1, T2) -> op(fun ?LEAF:difference/2, T1, T2).

-spec dnf(type()) -> S when S :: dnf().
dnf(T) ->
    dnf_acc([], [], [], T).

-spec dnf_acc(dnf(), [?ATOM:type()], [?ATOM:type()], bdd()) -> dnf().
dnf_acc(Acc, Ps, Ns, {leaf, T}) ->
    case ?LEAF:empty() of
        T -> Acc;
        _ -> [{Ps, Ns, T} | Acc]
    end;
dnf_acc(Acc, Ps, Ns, {node, A, P, N}) ->
    % We could add heuristics here to avoid adding some redundant atoms
    % but the downstream minimizer is cheap, so we don't need to
    Acc0 = dnf_acc(Acc, [A | Ps], Ns, P),
    dnf_acc(Acc0, Ps, [A | Ns], N).

-spec is_empty(type(), S) -> {boolean(), S} when S :: is_empty_cache().
is_empty(Ty, ST) ->
    Dnf = dnf(Ty),
    lists:foldl(fun
        (_Line, {false, ST0}) -> {false, ST0};
        (Line, {true, ST0}) -> is_empty_line(Line, ST0)
    end, {true, ST}, Dnf).

% tallying
-spec normalize(type(), monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when S :: normalize_cache().
normalize(Dnf, Fixed, ST) ->
    D = minimize_dnf(Dnf),

    case D of
        [] -> {constraint_set:sat(), ST};
        _ ->
            lists:foldl(fun
                (Line, {CurrentConstr, ST0}) ->
                    case constraint_set:unsat() of
                        CurrentConstr -> {constraint_set:unsat(), ST0};
                        _ ->
                            {ResConstr, ST1} = normalize_line(Line, Fixed, ST0),
                            Final = constraint_set:meet(CurrentConstr, ResConstr, Fixed),
                            {Final, ST1}
                    end
            end, {constraint_set:sat(), ST}, D)
    end.

% =============
% Unparse
% =============
-spec unparse(type(), T) -> {ast_ty(), T} when T :: unparse_cache().
unparse(Dnf, ST) ->
    {Empty, Any} = {empty(), any()},
    case Dnf of
        Empty -> {{predef, none}, ST};
        Any -> {{predef, any}, ST};
        _ ->
            {ToUnion, ST2} = lists:foldl(
                fun(Line, {Acc, ST0}) ->
                    {Ele, ST1} = unparse_line(Line, ST0),
                    {Acc ++ [Ele], ST1}
                end,
                {[], ST},
                minimize_dnf(Dnf)
            ),
            {ast_lib:mk_union(ToUnion), ST2}
    end.

-spec unparse_line(line(), S) -> {ast_ty(), S} when S :: unparse_cache().
unparse_line({Pos, Neg, Leaf}, C0) ->
    {Ps, C1} = lists:foldl(fun(P, {Acc, C00}) -> {Pp, C01} = ?ATOM:unparse(P, C00), {Acc ++ [Pp], C01} end, {[], C0}, Pos),
    {Ns, C2} = lists:foldl(fun(N, {Acc, C00}) -> {Nn, C01} = ?ATOM:unparse(N, C00), {Acc ++ [ast_lib:mk_negation(Nn)], C01} end, {[], C1}, Neg),
    {Lf, C3} = ?LEAF:unparse(Leaf, C2),

    {ast_lib:mk_intersection(Ps ++ Ns ++ [Lf]), C3}.

-spec all_variables(bdd(), all_variables_cache()) -> sets:set(variable()).
all_variables(Dnf, Cache) ->
    AllLines = dnf(Dnf),
    lists:foldl(fun({P, N, Leaf}, Atoms) ->
        sets:union([Atoms, all_variables_line(P, N, Leaf, Cache)])
    end, sets:new(), AllLines).

-spec minimize_dnf(type()) -> dnf().
minimize_dnf(T) ->
    minimize_node_dnf(dnf(T)).

-spec minimize_node_dnf(dnf()) -> dnf().
minimize_node_dnf([]) -> [];
minimize_node_dnf([X]) -> [X];
% only minimize dnfs with more than one line
minimize_node_dnf(Dnf) ->
    % with 0/1 (ty_bool) leaves there is a single '1' output 
    % with algebraic leaves the number of outputs is the number of
    % syntactically distinct non-empty leaves.
    Indexed = lists:enumerate(lists:uniq([Leaf || {_, _, Leaf} <- Dnf])),
    {AllOutputs, ReverseAllOutputs} = {#{Leaf => I || {I, Leaf} <- Indexed}, maps:from_list(Indexed)},
    O = maps:size(AllOutputs),

    % index every atom appearing in the on-set
    AllAtoms = #{Atom => [] || {Pos, Neg, _} <- Dnf, Atom <- Pos ++ Neg},
    I = maps:size(AllAtoms),
    IndexedAtom = lists:enumerate(maps:keys(AllAtoms)),
    {AtomIndices, RevAtomIndices} = {#{Atom => Ind || {Ind, Atom} <- IndexedAtom}, maps:from_list(IndexedAtom)},

    % each DNF line maps to exactly one (0-based) output leaf
    OnCubes = [ {[ maps:get(A, AtomIndices) - 1 || A <- Pos ],
       [ maps:get(A, AtomIndices) - 1 || A <- Neg ],
       [ maps:get(Leaf, AllOutputs) - 1 ]}
      || {Pos, Neg, Leaf} <- Dnf ],
    ResultCubes = dnf_minimizer:minimize(I, O, OnCubes),
    '_minimize_cubes_to_dnf'(ResultCubes, RevAtomIndices, ReverseAllOutputs).

% result cubes back to DNF lines 
% split a multi-leaf cube into one line per leaf
-spec '_minimize_cubes_to_dnf'([cube()], #{pos_integer() => ?ATOM:type()}, #{pos_integer() => ?LEAF:type()}) -> dnf().
'_minimize_cubes_to_dnf'(Cubes, RevAtomIndices, ReverseAllOutputs) ->
    [ {PosList, NegList, maps:get(Leaf + 1, ReverseAllOutputs)}
      || {Pos, Neg, Leaves} <- Cubes,
         PosList <- [[ maps:get(P + 1, RevAtomIndices) || P <- Pos ]],
         NegList <- [[ maps:get(N + 1, RevAtomIndices) || N <- Neg ]],
         Leaf <- Leaves ].


-spec has_negative_only_line(type()) -> boolean().
has_negative_only_line(T) ->
    D = minimize_dnf(T),
    lists:any(fun({[], [_|_], _}) -> true; (_) -> false end, D).
