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
  all_variables/2
]).

-export_type([type/0]).

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

-type monomorphic_variables() :: etally:monomorphic_variables().
-type set_of_constraint_sets() :: constraint_set:set_of_constraint_sets().
-type ast_ty() :: ast:ty().
-type variable() :: ty_variable:type().
-type cache() :: term(). %TODO
-type type() :: bdd().
-type line() :: {[?ATOM:type()], [?ATOM:type()], ?LEAF:type()}.
-type dnf() :: [line()].
-type leaf() :: {leaf, ?LEAF:type()}.
-type bdd() :: leaf() | {node, _Atom :: ?ATOM:type(), _PositiveEdge :: bdd(), _NegativeEdge :: bdd()}.

%% Reorders a potentially invalid BDD
%% TODO refactor, ugly
-spec reorder(bdd()) -> bdd().
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
    
  % Determine if we need to push this node down
  Z = case {PosAtom, NegAtom} of
    {undefined, undefined} -> {node, Atom, OrderedPos, OrderedNeg};
    _ -> 
      case PosAtom /= undefined andalso ?ATOM:compare(Atom, PosAtom) /= lt of
        true -> push_down(Atom, OrderedPos, OrderedNeg);
        _ -> 
          case NegAtom /= undefined andalso ?ATOM:compare(Atom, NegAtom) /= lt of
            true -> push_down(Atom, OrderedPos, OrderedNeg);
             _ -> {node, Atom, OrderedPos, OrderedNeg}
          end
        end 
    end,
  assert_valid(Z),
  Z.

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
-spec normalize(bdd()) -> bdd().
normalize(Bdd = {node, _Atom, Pos, Neg}) -> 
  case equal(Pos, Neg) of
    true -> Pos;
    false -> Bdd
  end;
normalize(X) -> X.

-spec op(fun((?LEAF:type(), ?LEAF:type()) -> ?LEAF:type()), bdd(), bdd()) -> bdd().
op(LeafOperation, Bdd1, Bdd2) ->
  is_ordered(Bdd1),
  is_ordered(Bdd2),
  Op = fun ROp(T1, T2) ->
    Res = 
    case {T1, T2} of
      {{leaf, L1}, {leaf, L2}} -> {leaf, LeafOperation(L1, L2)};
      {{leaf, L}, {node, A, P, N}} -> 
        {node, A, ROp({leaf, L}, P), ROp({leaf, L}, N)};
      {{node, A, P, N}, {leaf, L}} -> 
        {node, A, ROp(P, {leaf, L}), ROp(N, {leaf, L})};
      {{node, A1, P1, N1}, {node, A2, P2, N2}} ->
        case ?ATOM:compare(A1, A2) of
          lt -> {node, A1, ROp(P1, T2), ROp(N1, T2)};
          gt -> {node, A2, ROp(T1, P2), ROp(T1, N2)};
          eq -> {node, A1, ROp(P1, P2), ROp(N1, N2)}
        end
    end,
    normalize(Res)
  end,
  Z = Op(Bdd1, Bdd2),
  is_ordered(Z).

-spec union(bdd(), bdd()) -> bdd().
union(T1, T2) -> 
  op(fun ?LEAF:union/2, T1, T2).

-spec intersect(bdd(), bdd()) -> bdd().
intersect(T1, T2) -> 
  op(fun ?LEAF:intersect/2, T1, T2).

-spec difference(bdd(), bdd()) -> bdd().
difference(T1, T2) -> op(fun ?LEAF:difference/2, T1, T2).

-spec dnf(bdd()) -> dnf().
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

-spec is_empty(type(), S) -> {boolean(), S}.
is_empty(Ty, ST) ->
  Dnf = dnf(Ty),
  lists:foldl(fun
    (_Line, {false, ST0}) -> {false, ST0};
    (Line, {true, ST0}) -> is_empty_line(Line, ST0)
  end, {true, ST}, Dnf).

% tallying
-spec normalize(type(), monomorphic_variables(), S) -> {set_of_constraint_sets(), S}.
normalize(Dnf, Fixed, ST) ->
  DD = dnf(Dnf),
  D = minimize_dnf(DD),

  case D of
    [] -> {[[]], ST};
    _ ->
      lists:foldl(fun
        (_Line, {[], ST0}) -> {[], ST0};
        (Line, {CurrentConstr, ST0}) -> 
          {ResConstr, ST1} = normalize_line(Line, Fixed, ST0),
          Final = constraint_set:meet(CurrentConstr, ResConstr, Fixed),
          {Final, ST1}
      end, {[[]], ST}, (D))
  end.

% =============
% Unparse
% =============
-spec unparse(type(), T) -> {ast_ty(), T}.
unparse(Dnf, ST) ->
  {ToUnion, ST2} = lists:foldl(
                     fun(Line, {Acc, ST0}) -> {Ele, ST1} = unparse_line(Line, ST0), {Acc ++ [Ele], ST1} end, 
                     {[], ST}, 
                     dnf(Dnf)
                    ),
  {ast_lib:mk_union(ToUnion), ST2}.

-spec unparse_line({[T], [T], ?LEAF:type()}, T) -> {ast_ty(), T} when T :: ?ATOM:type().
unparse_line({Pos, Neg, Leaf}, C0) ->
  {Ps, C1} = lists:foldl(fun(P, {Acc, C00}) -> {Pp, C01} = ?ATOM:unparse(P, C00), {Acc ++ [Pp], C01} end, {[], C0}, Pos),
  {Ns, C2} = lists:foldl(fun(N, {Acc, C00}) -> {Nn, C01} = ?ATOM:unparse(N, C00), {Acc ++ [ast_lib:mk_negation(Nn)], C01} end, {[], C1}, Neg),
  {Lf, C3} = ?LEAF:unparse(Leaf, C2),

  {ast_lib:mk_intersection(Ps ++ Ns ++ [Lf]), C3}.


-spec all_variables(bdd(), cache()) -> sets:set(variable()).
all_variables(Dnf, Cache) ->
  AllLines = dnf(Dnf),
  lists:foldl(fun({P, N, Leaf}, Atoms) -> 
    sets:union([Atoms, all_variables_line(P, N, Leaf, Cache)]) 
  end, sets:new(), AllLines).

-spec minimize_dnf(dnf()) -> dnf().
minimize_dnf(Dnf) ->
  minimize_node_dnf(Dnf).

-spec minimize_node_dnf(dnf()) -> dnf().
minimize_node_dnf([]) -> [];
minimize_node_dnf([X]) -> [X];
% only minimize dnfs with more than one line
minimize_node_dnf(Dnf) ->
  % TAll = os:system_time(millisecond),
  % using espresso names
  AllVariables = lists:foldl(fun({Pos, Neg, _}, Env) -> 
    lists:foldl(fun(Term, Env2) -> Env2#{Term => []} end, Env, Pos ++ Neg)
                  end, #{}, Dnf),
  % .i length(AllVariables)
  I = maps:size(AllVariables),

  % when we have only 0/1 leafs, we look only at a single '1' output
  % with algebraic bdds, the amount of output functions 
  % is the amount of syntactically different leafs which are not 0
  {AllOutputs, ReverseAllOutputs, _} = lists:foldl(fun({_, _, T}, {Env, RevEnv, Index}) -> 
                                    case Env of
                                      #{T := _} -> {Env, RevEnv, Index};
                                      _ -> {Env#{T => Index}, RevEnv#{Index => T}, Index + 1}
                                    end
                  end, {#{}, #{}, 1}, Dnf),
  % .o length(AllOutputs)
  O = maps:size(AllOutputs),

  % now for all variables assign an index
  {_, VariableIndices, RevVariableIndices} = maps:fold(fun(K, _V, {Index, Vars, RevVars}) -> {Index+1, Vars#{K => Index}, RevVars#{Index => K}} end, {1, AllVariables, #{}}, AllVariables),

  % convert all lines using the variable indices
  AllLines = lists:foldl(fun({Pos, Neg, T}, All) -> 
     % variables
     MinTerm = list_to_tuple(lists:duplicate(I, "-")),
     NewMinTerm0 = lists:foldl(fun(P, Min) -> replace_index("1", P, Min, VariableIndices) end, MinTerm, Pos),
     NewMinTerm1 = lists:foldl(fun(N, Min) -> replace_index("0", N, Min, VariableIndices) end, NewMinTerm0, Neg),

     % replace a single output with 1
     MinTermOutputs = list_to_tuple(lists:duplicate(O, "0")),
     MinTermOutputsFin = erlang:setelement(maps:get(T, AllOutputs), MinTermOutputs, "1"),

     NewTWithoutOutputs = tuple_to_list(NewMinTerm1),
     Outputs = tuple_to_list(MinTermOutputsFin),
     [lists:flatten(NewTWithoutOutputs ++ " " ++ Outputs)] ++ All
                         end, [], Dnf),

  StrInput = ".i " ++ integer_to_list(I) ++ "\n.o " ++ integer_to_list(O) ++ "\n" ++ lists:flatten(lists:join("\n", AllLines)),
  
  % TODO IMPORTANT make sure binary is available! wasted 2 hours searching for a non-issue
  file:make_dir("/tmp/etylizer"),
  ok = file:write_file("/tmp/etylizer/espresso_input.pla", StrInput),
  % T0 = os:system_time(millisecond),
  Result = os:cmd(etylizer_main:get_espresso_binary() ++ " < /tmp/etylizer/espresso_input.pla"),
  % file:delete("/tmp/etylizer/espresso_input.pla"),

  % io:format(user,"~p ms~n", [os:system_time(millisecond) - T0]),
  OnlyResultLines = extract_integer_lines(Result, I + 1 + O),
  % Inn = [string:slice(L, 0, I + 1 + O) || L <- AllLines],
  % Out = extract_integer_lines(Result, I + 1 + O),
  E = [convert_back_to_repr(list_to_tuple(string:split(Line, " ")), RevVariableIndices, ReverseAllOutputs, 1, {[], [], to_replace}) || Line <- OnlyResultLines],
  E.

-spec replace_index(string(), [A], Line, #{A => integer()}) -> Line.
replace_index(Val, Term, CurrentLine, VariableIndices) ->
  erlang:setelement(maps:get(Term, VariableIndices), CurrentLine, Val).

-spec extract_integer_lines(string(), integer()) -> [string()].
extract_integer_lines(Str, Max) ->
    Lines = string:split(Str, "\n", all),
    [string:slice(Line,0, Max) || Line <- Lines, is_integer_start(Line)].

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
  [First, _Second] = string:split(Outputs, "1", all),
  Index = length(First) + 1,
  {P, N, maps:get(Index, IndexToOutput)};
convert_back_to_repr({[$- | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, Acc) -> 
  convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, Acc);
convert_back_to_repr({[$1 | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, {Pos, Neg, to_replace}) -> 
  convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, {Pos ++ [maps:get(CurrentIndex, IndexToTerms)], Neg, to_replace});
convert_back_to_repr({[$0 | Rest], Outputs}, IndexToTerms, IndexToOutput, CurrentIndex, {Pos, Neg, to_replace}) -> 
  convert_back_to_repr({Rest, Outputs}, IndexToTerms, IndexToOutput, CurrentIndex + 1, {Pos, Neg ++ [maps:get(CurrentIndex, IndexToTerms)], to_replace}).
