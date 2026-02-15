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

-etylizer({disable_exhaustiveness_toplevel, [convert_back_to_repr/5]}).

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
    % but espresso is so cheap, we don't need to do that
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
    DD = dnf(Dnf),
    D = minimize_dnf(DD),

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
                minimize_dnf(dnf(Dnf))
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

-spec minimize_dnf(S) -> S when S :: dnf().
minimize_dnf(Dnf) ->
    minimize_node_dnf(Dnf).

-spec minimize_node_dnf(dnf()) -> dnf().
minimize_node_dnf([]) -> [];
minimize_node_dnf([X]) -> [X];
% only minimize dnfs with more than one line
minimize_node_dnf(Dnf) ->
    % TAll = os:system_time(millisecond),
    % using espresso names
    AllVariables = '_minimize_vars_from_dnf'(Dnf),

    % .i length(AllVariables)
    I = maps:size(AllVariables),

    % when we have only 0/1 leafs, we look only at a single '1' output
    % with algebraic bdds, the amount of output functions
    % is the amount of syntactically different leafs which are not 0
    {AllOutputs, ReverseAllOutputs} = '_minimize_outputs_from_dnf'(Dnf),
    % .o length(AllOutputs)
    O = maps:size(AllOutputs),

    % now for all variables assign an index
    {VariableIndices, RevVariableIndices} = '_minimize_indices_from_variables'(AllVariables),

    % convert all lines using the variable indices
    AllLines = '_minimize_all_lines_from_dnf'(Dnf, VariableIndices, AllOutputs, I, O),
    StrInput = ".i " ++ integer_to_list(I) ++ "\n.o " ++ integer_to_list(O) ++ "\n" ++ lists:flatten(lists:join("\n", AllLines)),
    Result = '_minimize_espresso'(StrInput),
    '_minimize_get_result'(Result, I, O, RevVariableIndices, ReverseAllOutputs).

-spec '_minimize_vars_from_dnf'(dnf()) -> #{?ATOM:type() => []}.
'_minimize_vars_from_dnf'(Dnf) ->
    lists:foldl(fun({Pos, Neg, _}, Env) ->
        lists:foldl(fun(Term, Env2) -> Env2#{Term => []} end, Env, Pos ++ Neg)
    end, #{}, Dnf).

-spec '_minimize_outputs_from_dnf'(dnf()) -> {#{?LEAF:type() => pos_integer()}, #{pos_integer() => ?LEAF:type()}}.
'_minimize_outputs_from_dnf'(Dnf) ->
    {All, Reverse, _} = lists:foldl(fun({_, _, T}, {Env, RevEnv, Index}) ->
        case Env of
            #{T := _} -> {Env, RevEnv, Index};
            _ -> {Env#{T => Index}, RevEnv#{Index => T}, ?assert_type(Index + 1, pos_integer())}
        end
    end, {#{}, #{}, 1}, Dnf),
    {All, Reverse}.

-spec '_minimize_indices_from_variables'(#{?ATOM:type() => []}) -> {#{?ATOM:type() => pos_integer()}, #{pos_integer() => ?ATOM:type()}}.
'_minimize_indices_from_variables'(AllVariables) ->
    {_, VarInd, RevVarInd} = maps:fold(
        fun(K, _V, {Index, Vars, RevVars}) ->
            {?assert_type(Index+1, pos_integer()), Vars#{K => Index}, RevVars#{Index => K}}
        end, {1, #{}, #{}}, AllVariables),
    {VarInd, RevVarInd}.

-spec '_minimize_all_lines_from_dnf'(dnf(), #{?ATOM:type() => pos_integer()}, #{?LEAF:type() => pos_integer()}, non_neg_integer(), non_neg_integer()) -> [string()].
'_minimize_all_lines_from_dnf'(Dnf, VariableIndices, AllOutputs, I, O) ->
    lists:foldl(fun({Pos, Neg, T}, All) ->
        % variables
        MinTerm = list_to_tuple(lists:duplicate(I, "-")),
        NewMinTerm0 = lists:foldl(fun(P, Min) -> replace_index("1", P, Min, VariableIndices) end, MinTerm, Pos),
        NewMinTerm1 = lists:foldl(fun(N, Min) -> replace_index("0", N, Min, VariableIndices) end, NewMinTerm0, Neg),

        % replace a single output with 1
        MinTermOutputs = list_to_tuple(lists:duplicate(O, "0")),
        MinTermOutputsFin = erlang:setelement(maps:get(T, AllOutputs), MinTermOutputs, "1"),

        NewTWithoutOutputs = ?assert_type(tuple_to_list(NewMinTerm1), [string()]),
        Outputs = ?assert_type(tuple_to_list(MinTermOutputsFin), [string()]),
        [lists:flatten(NewTWithoutOutputs ++ " " ++ Outputs)] ++ All

    end, [], Dnf).

% "01-1001 1" -> {"01-1001", "1"}
-spec espresso_split_line_into_elements_and_result(string()) -> {string(), string()}.
espresso_split_line_into_elements_and_result(LineStr) ->
    case string:split(LineStr, " ") of
        [Elements, Result] -> {Elements, Result};
        _ -> error(badarg) % TODO mark non-exhaustive
    end.

-spec '_minimize_get_result'(string(), non_neg_integer(), non_neg_integer(), #{pos_integer() => ?ATOM:type()}, #{pos_integer() => ?LEAF:type()}) -> dnf().
'_minimize_get_result'(Result, I, O, RevVariableIndices, ReverseAllOutputs) ->
    OnlyResultLines = extract_integer_lines(Result, I + 1 + O),

    [
        convert_back_to_repr(
            espresso_split_line_into_elements_and_result(Line),
            RevVariableIndices,
            ReverseAllOutputs, 1, {[], [], to_replace})
        || Line <- OnlyResultLines
    ].

-spec '_minimize_espresso'(string()) -> string().
'_minimize_espresso'(StrInput) ->
    Path = espresso_bin:get_path(),
    Port = open_port({spawn_executable, Path}, [use_stdio, exit_status, stream, stderr_to_stdout]),
    % Append .e marker so espresso stops reading without needing EOF on stdin
    port_command(Port, ?assert_type([StrInput, "\n.e\n"], iodata())),
    '_collect_port_output'(Port, []).

-spec '_collect_port_output'(port(), string()) -> string().
'_collect_port_output'(Port, Acc) ->
    receive
        {Port, {data, Data}} ->
            '_collect_port_output'(Port, Acc ++ Data);
        {Port, {exit_status, 0}} ->
            Acc;
        {Port, {exit_status, Status}} ->
            error({espresso_exit, Status})
    end.

-spec replace_index(string(), A, tuple(), #{A => pos_integer()}) -> tuple().
replace_index(Val, Term, CurrentLine, VariableIndices) ->
    erlang:setelement(maps:get(Term, VariableIndices), CurrentLine, Val).

-spec extract_integer_lines(string(), non_neg_integer()) -> [string()].
extract_integer_lines(Str, Max) ->
    Lines = string:split(Str, "\n", all),
    lists:filtermap(
        fun(Line) ->
            case is_integer_start(Line) of
                false -> false;
                true -> {true, string:slice(Line,0, Max)}
            end
        end,
        Lines).

-spec is_integer_start(string()) -> boolean().
is_integer_start([C|_]) when C == $- -> true;
is_integer_start([C|_]) when C >= $0, C =< $9 -> true;
is_integer_start(_) -> false.

-spec convert_back_to_repr({string(), string()},
                           #{integer() => ?ATOM:type()},
                           #{integer() => ?LEAF:type()},
                           integer(),
                           {[?ATOM:type()], [?ATOM:type()], ?LEAF:type() | to_replace}) -> line().
convert_back_to_repr({[], Outputs}, _IndexToTerms, IndexToOutput, _CurrentIndex, {P, N, to_replace}) ->
    % assert only one "1" in outputs
    case string:split(Outputs, "1", all) of
        [First, _Second] ->
            Index = length(First) + 1,
            {P, N, maps:get(Index, IndexToOutput)};
        _ -> error(badarg) % TODO mark non-exhaustive
    end;
convert_back_to_repr({[$- | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, Acc) ->
    convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, Acc);
convert_back_to_repr({[$1 | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, {Pos, Neg, to_replace}) ->
    convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, {Pos ++ [maps:get(CurrentIndex, IndexToTerms)], Neg, to_replace});
convert_back_to_repr({[$0 | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, {Pos, Neg, to_replace}) ->
    convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, {Pos, Neg ++ [maps:get(CurrentIndex, IndexToTerms)], to_replace}).

-spec has_negative_only_line(type()) -> boolean().
has_negative_only_line(T) ->
    D = minimize_dnf(dnf(T)),
    lists:any(fun({[], [_|_], _}) -> true; (_) -> false end, D).
