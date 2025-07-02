% A generic BDD parameterized over both the 'nodes and 'leafs

-export([
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

% hide built-in Erlang node function
-compile({no_auto_import, [node/1]}).

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
  D = dnf(Dnf),
  case D of
    [] -> {[[]], ST};
    _ ->
      lists:foldl(fun
        (_Line, {[], ST0}) -> {[], ST0};
        (Line, {CurrentConstr, ST0}) -> 
          {ResConstr, ST1} = normalize_line(Line, Fixed, ST0),
          {constraint_set:meet(CurrentConstr, ResConstr, Fixed), ST1}
      end, {[[]], ST}, D)
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

-spec unparse_line({[T], [T], ?LEAF:type()}, T) -> {boolean(), T} when T :: ?ATOM:type().
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
