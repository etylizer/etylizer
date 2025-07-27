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
-type dnf() :: [{[?ATOM:type()], [?ATOM:type()], ?LEAF:type()}].
-type leaf() :: {leaf, ?LEAF:type()}.
-type bdd() :: leaf() | {node, _Atom :: ?ATOM:type(), _PositiveEdge :: bdd(), _NegativeEdge :: bdd()}.

%% Reorders a potentially invalid BDD
%% TODO refactor, ugly
-spec reorder(bdd()) -> bdd().
reorder({leaf, Value}) -> {leaf, ?LEAF:reorder(Value)};
reorder(B = {node, Atom, Pos, Neg}) ->
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
  assert_valid(case {PosAtom, NegAtom} of
    {undefined, undefined} -> {node, Atom, OrderedPos, OrderedNeg};
    _ -> 
      case PosAtom /= undefined andalso ?ATOM:compare(Atom, PosAtom) == gt of
        true -> push_down(Atom, OrderedPos, OrderedNeg);
        _ -> 
          case NegAtom /= undefined andalso ?ATOM:compare(Atom, NegAtom) == gt of
            true -> push_down(Atom, OrderedPos, OrderedNeg);
             _ -> {node, Atom, OrderedPos, OrderedNeg}
          end
        end 
    end).
               

push_down(TopAtom, Pos, Neg) -> 
  union( 
    intersect(singleton(TopAtom), Pos),
    intersect(negate(singleton(TopAtom)), Neg)
  ).

assert_valid(Bdd) -> is_ordered(Bdd).

-spec is_ordered(bdd()) -> boolean().
is_ordered(Bdd = {leaf, T}) -> ?LEAF:assert_valid(T), Bdd;
is_ordered(Bdd = {node, Atom, PositiveEdge, NegativeEdge}) ->
  % Check that all atoms in positive and negative edges are smaller than current atom
  check_branch(Atom, PositiveEdge),
  check_branch(Atom, NegativeEdge),
  % check the subtrees
  is_ordered(PositiveEdge),
  is_ordered(NegativeEdge),
  Bdd.

-spec check_branch(?ATOM:type(), bdd()) -> _.
check_branch(_ParentAtom, Bdd = {leaf, _}) -> ok;
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
negate(Bdd1 = {leaf, A}) -> {leaf, ?LEAF:negate(A)};
negate(Bdd1 = {node, Atom, Pos, Neg}) -> {node, Atom, negate(Pos), negate(Neg)}.

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
        % io:format(user,"Compare: ~w and ~w: ~p~n", [A1, A2, ?ATOM:compare(A1, A2)]),
        case ?ATOM:compare(A1, A2) of
          lt ->
            % io:format(user,"A1 is less than, putting A1 first:~w < ~w~n", [A1, A2]),
            {node, A1, ROp(P1, T2), ROp(N1, T2)};
          gt ->
            % io:format(user,"A2 is greater than, putting A2 first~n", []),
            {node, A2, ROp(T1, P2), ROp(T1, N2)};
          eq ->
            {node, A1, ROp(P1, P2), ROp(N1, N2)}
        end
    end,
    normalize(Res)
  end,
  Z = Op(Bdd1, Bdd2),
  % io:format(user,"Doing OP: ~p on~n~p~n~p~nResult:~p~n", [LeafOperation, Bdd1, Bdd2, Z]),
  is_ordered(Z).

-spec union(bdd(), bdd()) -> bdd().
union(T1, T2) -> 
  op(fun ?LEAF:union/2, T1, T2).

-spec intersect(bdd(), bdd()) -> bdd().
intersect(T1, T2) -> 
  % io:format(user,"~p~n",[{T1, T2}]),
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
  % TODO small heuristic add
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
  ?INSIDE(dnf_ty_tuple, 
          io:format(user,"Current: ~p~n", [Dnf])
                   ),
  D = minimize_dnf(DD),

  case D of
    [] -> {[[]], ST};
    _ ->
      lists:foldl(fun
        (_Line, {[], ST0}) -> {[], ST0};
        (Line, {CurrentConstr, ST0}) -> 
                      {Time, {ResConstr, ST1}} = timer:tc(fun() -> normalize_line(Line, Fixed, ST0) end, millisecond),
          Final = constraint_set:meet(CurrentConstr, ResConstr, Fixed),
          % ?INSIDE(dnf_ty_tuple, 
          %         io:format(user,"Line: ~p~nResult: ~p~n", [Line, ResConstr])
          %                  ),
          % ?INSIDE(dnf_ty_tuple, 
          %         io:format(user,"Final: ~p~n", [Final])
          %                  ),
          % case ResConstr of
          %   [[]] -> ok;
          %   _ -> 
          %     ok
          %     % io:format(user,"Current: ~p~n", [length(ResConstr)]),
          %     % io:format(user,"Current -> Next: ~p -> ~p~n", [length(CurrentConstr), length(Final)])
          %     % io:format(user,"~nCurrent -> Next: ~p -> ~p~n(~p ms) ~w~n", [length(CurrentConstr), length(Final), Time, (ResConstr)])
          % end),
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

minimize_dnf(Dnf) ->
  case ?MODULE of
    % dnf_ty_variable -> minimize_var_dnf(Dnf);
    dnf_ty_tuple -> minimize_node_dnf(Dnf);
    dnf_ty_function -> minimize_node_dnf(Dnf);
    _ -> Dnf
  end.

% minimize function for first layer BDDs (variables)
minimize_var_dnf([]) -> [];
minimize_var_dnf([X]) -> [X];
minimize_var_dnf(Dnf) ->
  AllVariables = lists:foldl(fun({Pos, Neg, _}, Env) -> 
    lists:foldl(fun(Term, Env2) -> Env2#{Term => []} end, Env, Pos ++ Neg)
                  end, #{}, Dnf),
  % .i length(AllVariables)
  I = maps:size(AllVariables),

  AllOutputs = lists:foldl(fun({_, _, T}, Env) -> 
                               Env#{T => []}
                  end, #{}, Dnf),
  % .o length(AllOutputs)
  O = maps:size(AllOutputs),

  error({Dnf, AllVariables, AllOutputs}),
  Dnf.

% minimize function for second layer BDDs
minimize_node_dnf([]) -> [];
minimize_node_dnf([X]) -> [X];
% only minimize dnfs with more than one line
minimize_node_dnf(Dnf) ->
  % T0 = os:system_time(millisecond),
  % using espresso names
  AllVariables = lists:foldl(fun({Pos, Neg, _}, Env) -> 
    lists:foldl(fun(Term, Env2) -> Env2#{Term => []} end, Env, Pos ++ Neg)
                  end, #{}, Dnf),
  % .i length(AllVariables)
  I = maps:size(AllVariables),

  % we have only 0/1 leafs, so we look only at '1' outputs
  % with algebraic bdds, the amount of output functions 
  % is the amount of syntactically different leafs which are not 0
  AllOutputs = lists:foldl(fun({_, _, T}, Env) -> 
                               Env#{T => []}
                  end, #{}, Dnf),
  % .o length(AllOutputs)
  O = maps:size(AllOutputs),

  % now for all variables assign an index
  % TODO list comprehension zip?
  {_, VariableIndices, RevVariableIndices} = maps:fold(fun(K, V, {Index, Vars, RevVars}) -> {Index+1, Vars#{K => Index}, RevVars#{Index => K}} end, {1, AllVariables, #{}}, AllVariables),

  % convert all lines using the variable indices
  AllLines = lists:foldl(fun({Pos, Neg, _}, All) -> 
                             MinTerm = list_to_tuple(lists:duplicate(I, "-") ++ " 1"),
                             NewMinTerm0 = lists:foldl(fun(P, Min) -> replace_index("1", P, Min, VariableIndices) end, MinTerm, Pos),
                             NewMinTerm1 = lists:foldl(fun(N, Min) -> replace_index("0", N, Min, VariableIndices) end, NewMinTerm0, Neg),
                             [lists:flatten(tuple_to_list(NewMinTerm1))] ++ All
                         end, [], Dnf),

  StrInput = ".i " ++ integer_to_list(I) ++ "\n.o 1\n" ++ lists:flatten(lists:join("\n", AllLines)),

  
  file:write_file("espresso_input.pla", StrInput),
  T0 = os:system_time(millisecond),
  Result = os:cmd("./espresso < espresso_input.pla"),
  io:format(user,"~p ms~n", [os:system_time(millisecond) - T0]),
  OnlyResultLines = extract_integer_lines(Result, I),
  Inn = [string:slice(L, 0, I) || L <- AllLines],
  Out = extract_integer_lines(Result, I),
  E = [convert_back_to_repr(Line, RevVariableIndices, 1, {[], [], 1}) || Line <- OnlyResultLines],
  case Inn /= Out of
    true -> 
      io:format(user,"Inn raw:~n~p~n", [Dnf]),
      io:format(user,"Inn: ~p~n", [Inn]),
      io:format(user,"Out: ~p~n", [Out]),
      io:format(user,"~p ms~n", [os:system_time(millisecond) - T0]);
    _ -> 
      ok 
  end,
  E.

replace_index(Val, Term, CurrentLine, VariableIndices) ->
  erlang:setelement(maps:get(Term, VariableIndices), CurrentLine, Val).

extract_integer_lines(Str, Max) ->
    Lines = string:split(Str, "\n", all),
    [string:slice(Line,0, Max) || Line <- Lines, is_integer_start(Line)].

is_integer_start([C|_]) when C >= $0, C =< $9 -> true;
is_integer_start(_) -> false.


convert_back_to_repr([], IndexToTerms, CurrentIndex, Acc) -> Acc;
convert_back_to_repr([$- | Rest], IndexToTerms, CurrentIndex, Acc) -> convert_back_to_repr(Rest, IndexToTerms, CurrentIndex + 1, Acc);
convert_back_to_repr([$1 | Rest], IndexToTerms, CurrentIndex, {Pos, Neg, 1}) -> convert_back_to_repr(Rest, IndexToTerms, CurrentIndex + 1, {Pos ++ [maps:get(CurrentIndex, IndexToTerms)], Neg, 1});
convert_back_to_repr([$0 | Rest], IndexToTerms, CurrentIndex, {Pos, Neg, 1}) -> convert_back_to_repr(Rest, IndexToTerms, CurrentIndex + 1, {Pos, Neg ++ [maps:get(CurrentIndex, IndexToTerms)], 1}).
