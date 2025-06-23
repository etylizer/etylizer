% A generic BDD parameterized over both the 'nodes and 'leafs
% 
% hide built-in Erlang node function
-compile([export_all, nowarn_export_all]).
-compile({no_auto_import, [node/1]}).

-ifndef(ATOM).
-define(ATOM, ty_bool).
-endif.
-ifndef(LEAF).
-define(LEAF, ty_bool).
-endif.

-type dnf() :: term(). % TODO
-type bdd() ::
  {leaf, ?LEAF:type()}
  | {node, _Atom :: ?ATOM:type(), _PositiveEdge :: bdd(), _NegativeEdge :: bdd()}.

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

-spec equal(bdd(), bdd()) -> bdd().
equal({node, A1, P1, N1}, {node, A2, P2, N2}) ->
  ?ATOM:equal(A1, A2) andalso equal(P1, P2) andalso equal(N1, N2);
equal({leaf, T1}, {leaf, T2}) ->
  ?LEAF:equal(T1, T2);
equal(_, _) ->
  false.

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
negate({leaf, A}) ->
  {leaf, ?LEAF:negate(A)};
negate({node, Atom, Pos, Neg}) -> 
  {node, Atom, negate(Pos), negate(Neg)}.


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
          lt ->
            {node, A1, ROp(P1, T2), ROp(N1, T2)};
          gt ->
            {node, A2, ROp(T1, P2), ROp(T1, N2)};
          eq ->
            {node, A1, ROp(P1, P2), ROp(N1, N2)}
        end
    end,
    normalize(Res)
  end,
  Op(Bdd1, Bdd2).

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

is_empty(Ty, ST) ->
  Dnf = dnf(Ty),
  lists:foldl(fun
    (_Line, {false, ST0}) -> {false, ST0};
    (Line, {true, ST0}) -> is_empty_line(Line, ST0)
  end, {true, ST}, Dnf).

% tallying
normalize(Dnf, Fixed, ST) ->
  D = dnf(Dnf),
  case D of
    [] -> {[[]], ST};
    _ ->
      % case ?MODULE of
      %   dnf_ty_tuple ->
      %     io:format(user,"~p Normalize the dnf~n~p~n", [?MODULE, D]);
      %   _ -> ok
      % end,
      % io:format(user,"[~p] normalize:~n~p~n", [?MODULE, D]),
      % single out variable
      {Cs, STf} = lists:foldl(fun
        (_Line, {[], ST0}) -> {[], ST0};
        (Line, {CurrentConstr, ST0}) -> 
          {ResConstr, ST1} = normalize_line(Line, Fixed, ST0),
          %io:format(user,"[~p] Single step result:~n~p~nMeet with~n~p~n", [?MODULE, ResConstr, CurrentConstr]),
          {constraint_set:meet(CurrentConstr, ResConstr), ST1}
      end, {[[]], ST}, D),

      %io:format(user,"Normalized finished:~n~p~n", [Cs]),
      {Cs, STf}
  end.

% =============
% Unparse
% =============
unparse(Dnf, Cache) ->
  ast_lib:mk_union(lists:map(fun(Line) -> unparse_line(Line, Cache) end, dnf(Dnf))).

unparse_line({Pos, Neg, Leaf}, Cache) ->
  ast_lib:mk_intersection(
   [?ATOM:unparse(P, Cache) || P <- Pos] 
   ++ [ast_lib:mk_negation(?ATOM:unparse(N, Cache)) || N <- Neg]
   ++ [?LEAF:unparse(Leaf, Cache)]
  ).

% do_dnf({node, Element, Left, Right}, F = {_Process, Combine}, Pos, Neg) ->
%   % heuristic: if Left is positive & 1, skip adding the negated Element to the right path
%   case {terminal, ?TERMINAL:any()} of
%     Left ->
%       F1 = fun() -> do_dnf(Left, F, [Element | Pos], Neg) end,
%       F2 = fun() -> do_dnf(Right, F, Pos, Neg) end,
%       Combine(F1, F2);
%     _ ->
%       F1 = fun() -> do_dnf(Left, F, [Element | Pos], Neg) end,
%       F2 = fun() -> do_dnf(Right, F, Pos, [Element | Neg]) end,
%       Combine(F1, F2)
%   end;

