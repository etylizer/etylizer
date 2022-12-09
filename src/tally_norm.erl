-module(tally_norm).

-import(stdtypes, [tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, tfun1/2, trange/2,
tunion/1, tunion/2, tintersect/1, trange_any/0, ttuple/1, tany/0, tnone/0,
tint/0, tint/1, ttuple1/1, tinter/1, tinter/2, tlist/1, tempty_list/0]).

-include_lib("log.hrl").

-export([
  norm_api/3
]).

-spec norm_api(constr:simp_constrs(), sets:new(), symtab:t()) -> any() | {fail, norm}.
norm_api(Constraints, Fix, Sym) ->

  Start = erlang:system_time(),
  ToMeetNormalizedConstraints =
    sets:fold(fun (Cs, Ac) -> normalize_constraints_api(Cs, Ac, Fix, Sym) end, [[]], Constraints),

  Middle = erlang:system_time(),
%%  logger:notice("Phase I ~p", [(Middle - Start)/1000000000]),

  SaturatedConstraints = saturate(ToMeetNormalizedConstraints, [], Fix, Sym),

  End = erlang:system_time(),

%%  logger:notice("Phase II ~p", [(End - Middle)/1000000000]),

  SaturatedConstraints.



normalize_constraints_api({csubty, _, S, T}, AllNormalized, Fix, Sym) ->
  SnT = tintersect([S, tnegate(T)]),

  % sorted list of merged variables => [{V, S, T}]
  Normalized = norm_and_merge(SnT, [], Fix, Sym),
  sanity(Normalized),
  M = merge_and_meet(Normalized, AllNormalized, Sym),
  M.


norm_and_merge(Ty, Memo, Fix, Sym) ->
  H1 = erlang:phash2(Ty),

  memoize:memo_fun(
    {norm_memo, H1},
    fun() ->
      T_partitions = dnf:simplify(subty:simple_empty(Ty, Sym)),
      case T_partitions of
        [] -> [[]]; % satisfiable
        _ ->
          {_ZeroPartitions, UnknownPartitions} = partition(T_partitions, Memo),
          case UnknownPartitions of
            [] -> [[]]; % satisfiable, memoized everything
            _ ->
              % TODO unfold recursive types once
              % necessary to transform back to AST, unfold, then partition again
              %%  T_ast  = partition_to_ast(UnknownPartitions),
              %%  T_norec = Ty, %esubrel:unfold_recursive_types(SymbolicTable, T_ast),

              norm_partitions(UnknownPartitions, Memo ++ UnknownPartitions, Fix, Sym)
          end
      end
    end
  ).

norm_partitions([], _Memo, _, _Sym) -> [[]]; % satisfiable constraints
norm_partitions([P | Ps], Memo, Fix, Sym) ->
  case norm_single_partition(P, Memo, Fix, Sym) of
    [] -> []; % unsatisfiable constraints
    All ->
      sanity(All),
      New = fun() -> norm_partitions(Ps, Memo, Fix, Sym) end,
      lazy_meet(All, New, Sym)
  end.



norm_single_partition({{P, []}, {N, []}}, Memo, Fix, Sym) ->
  SimpleSubty = fun(Pp, Nn) -> case subty:is_subty(Sym, stdtypes:tintersect(Pp), stdtypes:tunion(Nn)) of true -> [[]]; _    -> [] end end,

  case P of
    [] -> []; % unsatisfiable constraints
    % === ATOMS & INTS & special
    [A | _] when
      A == {predef, atom};
      A == {predef, integer};
      A == {predef, float};
      A == {empty_list} ->
      SimpleSubty(P, N);
    [{singleton, Atom} | _] when is_atom(Atom); is_integer(Atom) -> SimpleSubty(P, N);
    [{range, _,_} | _] -> SimpleSubty(P, N);
    [{left, _} | _] -> SimpleSubty(P, N);
    [{right, _} | _] -> SimpleSubty(P, N);

    % empty tuples can be decided immediately, like atoms
    [{tuple, []} | _Ps] ->
      case [Z || Z <- N, is_ttuple(Z, 0)] of
        [] -> []; % not empty, unsatisfiable
        [{tuple, []}] -> [[]] % empty, satisfiable
      end;

    % === LIST A B
    [{improper_list, _, _} | _Ps] ->
      FilteredNegativeAtoms = lists:filter(fun stdtypes:is_tlist/1, N),
      norm_list(P, FilteredNegativeAtoms, Memo, Fix, Sym);


    [{tuple, L} | _Ps] ->
      norm_tuple(length(L), P, [X || X <- N, is_ttuple(X, length(L))], Memo, Fix, Sym)
    ;

    [{fun_full, C, _} | _Ps] ->
      norm_fun_full(length(C), P, [X || X <- N, is_tfun_full(X, length(C))], Memo, Fix, Sym);

    [Pp | _Ps] ->
      logger:debug("Unhandled normalization of atom type:~n~p", [Pp]),
      throw(todo)
  end;


norm_single_partition({{P, Pv}, {N, Nv}}, Memo, Fix, Sym) ->
  SimpleSubty = fun(Pp, Nn) -> case subty:is_subty(Sym, stdtypes:tintersect(Pp), stdtypes:tunion(Nn)) of true -> [[]]; _ -> [] end end,

  % if {P,N} is empty by itself already, variable assignment does not matter
  case SimpleSubty(P, N) of
    [[]] -> [[]];
    _ ->
      sanity(single_out(P, N, Pv, Nv, Memo, Fix, Sym))
  end.

norm_fun_full(_Length, _Ps, [], _Memo, _, _Sym) -> []; % not empty
norm_fun_full(Length, Ps, [{fun_full, NDomains, NCodomain} | Ns], Memo, Fix, Sym) ->
  % treat multi argument as tuple
  NDomainsTuple = {tuple, NDomains},

  PDomainsTuple = {union, [{tuple, Domains} || {fun_full, Domains, _} <- Ps]},

  Tx = tintersect([NDomainsTuple, tnegate(PDomainsTuple)]),
  CounterExample = fun() -> norm_and_merge(Tx, Memo, Fix, Sym) end,

  Others = fun() -> norm_fun_full_explore(NDomainsTuple, stdtypes:tnegate(NCodomain), Ps, Memo, Fix, Sym) end,
  Con1 = lazy_meet(CounterExample, Others, Sym),

  % if not, continue searching for another arrow in N
  FullSearch = fun() -> norm_fun_full(Length, Ps, Ns, Memo, Fix, Sym) end,

  lazy_join(Con1, FullSearch, Sym).

norm_fun_full_explore(NDomains, NCodomain, [], Memo, Fix, Sym) ->
  Con1 = fun() -> norm_and_merge(NDomains, Memo, Fix, Sym) end,
  Con2 = fun() -> norm_and_merge(NCodomain, Memo, Fix, Sym) end,
  lazy_join(Con1, Con2, Sym);

norm_fun_full_explore(NDomains, NCodomain, [{fun_full, From, S2} | P], Memo, Fix, Sym) ->

  S1 = {tuple, From},
  Tx1 = tintersect([NDomains, tnegate(S1)]),
  OptCon1 = fun() -> norm_and_merge(Tx1, Memo, Fix, Sym) end,

  BigIntersectionCoDomain = {intersection, [CoDomain || {fun_full, _, CoDomain} <- P]},
  Tx2 = tintersect([BigIntersectionCoDomain, NCodomain]),
  OptCon2 = fun() -> norm_and_merge(Tx2, Memo, Fix, Sym) end,
  OptCon = lazy_join(OptCon1, OptCon2, Sym),

  Con1 = fun() -> norm_fun_full_explore(NDomains, tintersect([S2, NCodomain]), P, Memo, Fix, Sym) end,
  Con2 = fun() -> norm_fun_full_explore(Tx1, NCodomain, P, Memo, Fix, Sym) end,

  Res = lazy_meet(OptCon, Con1, Sym),
  lazy_meet(Res, Con2, Sym).




norm_tuple(Length, Ps, Ns, Memo, Fix, Sym) ->
  % T_i intersections
  T_is = [ {intersection, [lists:nth(Index, Components) || {tuple, Components} <- Ps]} || Index <- lists:seq(1, Length) ],


  % either all n-components (of Ps) are equated to empty for every n
  EmptynessPosComponents = lists:foldl(fun(Tx, Res) ->
    Con1 = fun() -> norm_and_merge(Tx, Memo, Fix, Sym) end,
    lazy_join(Res, Con1, Sym)
              end, [], T_is),


  % or explore all possibilities of negated Ns
  ExploreConstraints = fun() -> norm_tuple_explore(Length, T_is, Ns, Memo, Fix, Sym) end,
  lazy_join(EmptynessPosComponents, ExploreConstraints, Sym).



norm_tuple_explore(_Length, _T_is, [], _Memo, _Fix, _Sym) -> [];
norm_tuple_explore(Length, T_is, [{tuple, N} | Ns], Memo, Fix, Sym) ->
  GenerateEmptynessConstraints = fun
                                   (_, []) -> [];
                                   ({Index, {PComponent, NComponent}}, Result) ->
                                     % either P & !N is empty at index i

                                     TiCap = tintersect([PComponent, tnegate(NComponent)]),
                                     TiCon1 = fun() -> norm_and_merge(TiCap, Memo, Fix, Sym) end,

                                     % OR
                                     % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
                                     ExploreCons = begin
                                                     DoDiff = fun({IIndex, PComp}) ->
                                                       case IIndex of
                                                         Index ->
                                                           tintersect([PComp, tnegate(NComponent)]);
                                                         _ ->
                                                           PComp
                                                       end
                                                              end,
                                                     NewPs = lists:map(DoDiff, lists:zip(lists:seq(1, length(T_is)), T_is)),
                                                     fun() -> norm_tuple_explore(Length, NewPs, Ns, Memo, Fix, Sym) end
                                                   end,


                                     UnionResult = lazy_join(TiCon1, ExploreCons, Sym),
                                     lazy_meet(Result, UnionResult, Sym)
                                 end,

  lists:foldl(GenerateEmptynessConstraints, [[]], lists:zip(lists:seq(1, Length), lists:zip(T_is, N))).


norm_list(Ps, Ns, Memo, Fix, Sym) ->
  T1 = {intersection, [X || {improper_list, X, _} <- Ps]},
  T2 = {intersection, [X || {improper_list, _, X} <- Ps]},
  Cons1 = fun() -> norm_and_merge(T1, Memo, Fix, Sym) end,
  Cons2 = fun() -> norm_and_merge(T2, Memo, Fix, Sym) end,

  Con0 = fun() -> norm_list_ext(T1, T2, Ns, Memo, Fix, Sym) end,

  Comps = lazy_join(Cons1, Cons2, Sym),
  lazy_join(Comps, Con0, Sym).

norm_list_ext(_T1, _T2, [], _Memo, _, _Sym) -> [];
norm_list_ext(T1, T2, [{improper_list, S1, S2} | Ns], Memo, Fix, Sym) ->
  T1Cap = tintersect([T1, tnegate(S1)]),
  T2Cap = tintersect([T2, tnegate(S2)]),

  Con1 = fun() -> norm_and_merge(T1Cap, Memo, Fix, Sym) end,
  Con10 = fun() -> norm_list_ext(T1Cap, T2, Ns, Memo, Fix, Sym) end,
  Con11 = lazy_join(Con1, Con10, Sym),

  Con22 = fun() ->
    Con2 = fun() -> norm_and_merge(T2Cap, Memo, Fix, Sym) end,
    Con20 = fun() -> norm_list_ext(T1, T2Cap, Ns, Memo, Fix, Sym) end,
    lazy_join(Con2, Con20, Sym)
          end,

  lazy_meet(Con11, Con22, Sym).


merge_and_meet([], _Set2, _Sym) -> [];
merge_and_meet(_Set1, [], _Sym) -> [];
merge_and_meet([[]], Set2, _Sym) -> Set2;
merge_and_meet(Set1, [[]], _Sym) -> Set1;
merge_and_meet(La, Lb, Sym) ->
  {H1, H2} = {erlang:phash2(La), erlang:phash2(Lb)},

  memoize:memo_fun(
    {norm_meet, {H1, H2}},
    fun() ->
      R = lists:map(fun(E) -> unionlist(Lb, E, Sym) end, La),
      R2 = lists:foldl(fun(NewS, All) -> merge_and_join(NewS, All, Sym) end, [], R),
      sanity(R2),
      R2
      end).



unionlist(L, A, Sym) -> lists:map(fun(E) -> union(A, E, Sym) end, L).


union([], L, _Sym) -> L;
union(L, [], _Sym) -> L;
union([{V1, T1, T2} | C1], [{V2, S1, S2} | C2], Sym) when V1 == V2 ->
  Lower = subty:simple_empty(dnf:partitions_to_ty(dnf:simplify(subty:simple_empty(tunion(T1, S1), Sym))), Sym),
  Upper = subty:simple_empty(dnf:partitions_to_ty(dnf:simplify(subty:simple_empty(tinter(T2, S2), Sym))), Sym),

%%  logger:warning("CONS ~p ~p ~p ~n~p", [Lower, V1, Upper, subty:is_subty(Sym, Lower, Upper)]),
%%  case subty:is_subty(Sym, Lower, Upper) of
%%    false ->
%%      logger:warning("Lower bound is bigger than upper bound!"),
%%      throw(todo),
%%      [];
%%    _ ->
      [{V1, Lower, Upper}] ++ union(C1, C2, Sym);
%%  end;
union([Z = {V1, _, _} | C1], S = [{V2, _, _} | _C2], Sym) when V1 < V2 ->
  [Z] ++ union(C1, S, Sym);
union(S = [{_, _, _} | _C1], [Z = {_, _, _} | C2], Sym) ->
  [Z] ++ union(C2, S, Sym).




merge_and_join([[]], _Set2, _Sym) -> [[]];
merge_and_join(_Set1, [[]], _Sym) -> [[]];
merge_and_join([], Set2, _Sym) -> Set2;
merge_and_join(Set1, [], _Sym) -> Set1;
merge_and_join(S1, S2, Sym) ->
  {H1, H2} = {erlang:phash2(S1), erlang:phash2(S2)},
  memoize:memo_fun(
    {norm_join, {H1, H2}},
    fun() ->
      MayAdd = fun (S, Con) -> (not (has_smaller_constraint(Con, S, Sym))) end,
      S22 = lists:filter(fun(C) -> MayAdd(S1, C) end, S2),
      S11 = lists:filter(fun(C) -> MayAdd(S22, C) end, S1),
      lists:map(fun lists:usort/1, lists:usort(S11 ++ S22))

    end).

has_smaller_constraint(_Con, [], _Sym) -> false;
has_smaller_constraint(Con, [C | S], Sym) ->
  case is_smaller(C, Con, Sym) of
    true -> true;
    _ -> has_smaller_constraint(Con, S, Sym)
  end.

% C1 and C2 are sorted by variable order
is_smaller([], _C2, _Sym) -> true;
is_smaller(_C1, [], _Sym) -> false;
is_smaller([{V1, T1, T2} | C1], [{V2, S1, S2} | C2], Sym) when V1 == V2 ->
  case subty:is_subty(Sym, T1, S1) andalso subty:is_subty(Sym, S2, T2) of
    true -> is_smaller(C1, C2, Sym);
    _ -> false
  end;
is_smaller([{V1, _, _} | _C1], [{V2, _, _} | _C2], _Sym) when V1 < V2 ->
  % V1 is not in the other set
  % not smaller
  false;
is_smaller(C1, [{_V2, _, _} | C2], Sym) ->
  is_smaller(C1, C2, Sym).



% sets are sorted by variable ordering
sanity(SetOfConstraints) ->
  AllVars = [V || {V, _, _} <- SetOfConstraints],
  true = length(AllVars) == length(lists:usort(AllVars)),
  SetOfConstraints.



% RUNTIME IRRELEVANT FUNCTIONS
lazy_meet(M1, M2, Sym) when not is_function(M1), is_function(M2) -> lazy_meet(fun() -> M1 end, M2, Sym);
lazy_meet(M1, M2, Sym) when is_function(M1), not is_function(M2) -> lazy_meet(M1, fun() -> M2 end, Sym);
lazy_meet(M1, M2, Sym) when not is_function(M1), not is_function(M2) -> lazy_meet(fun() -> M1 end, fun() -> M2 end, Sym);
% everything is fun
lazy_meet(M1, M2, Sym) ->
  case M1() of
    [] ->
      [];
    Res ->
      merge_and_meet(Res, M2(), Sym)
  end.

lazy_join(M1, M2, Sym) when not is_function(M1), is_function(M2) -> lazy_join(fun() -> M1 end, M2, Sym);
lazy_join(M1, M2, Sym) when is_function(M1), not is_function(M2) -> lazy_join(M1, fun() -> M2 end, Sym);
lazy_join(M1, M2, Sym) when not is_function(M1), not is_function(M2) -> lazy_join(fun() -> M1 end, fun() -> M2 end, Sym);
% everything is fun
lazy_join(M1, M2, Sym) ->
  case M1() of
    [[]] ->
      [[]];
    Res ->
      merge_and_join(Res, M2(), Sym)
  end.



ord(P, N, Fix) ->
  % fixed variables are higher order than all non-fixed ones
  Pp = [{X, pos} || X = {var, V} <- P, not sets:is_element(V, Fix)],
  Nn = [{X, neg} || X = {var, V} <- N, not sets:is_element(V, Fix)],
  % positive or negative does not matter, variables are thrown away
  Rest = [{X, pos} || X = {var, V} <- P ++ N, sets:is_element(V, Fix)],

  All = lists:sort(Pp) ++ lists:sort(Nn) ++ lists:sort(Rest),

  case All of
    [] -> {fail, none};
    [X | _] -> X
  end.


single_out(P, N, Pv, Nv, Memo, Fix, Sym) ->
  SmallestVar = ord(lists:sort(Pv), lists:sort(Nv), Fix),
  case single_out_variable(P, N, Pv, Nv, SmallestVar, Memo, Fix, Sym) of
    fail -> [];
    {delta, R} -> R;
    X -> [[X]] % sorted
  end.

partition(Partitions, []) -> {[], Partitions};
partition(Partitions, Memo) -> {_Empty, _Unknown} = lists:partition(fun(Part) -> lists:member(Part, Memo) end, Partitions).
is_ttuple({tuple, L}, TupleArity) -> length(L) == TupleArity;
is_ttuple(_, _) -> false.
is_tfun_full({fun_full, L, _T}, Arity) -> length(L) == Arity;
is_tfun_full(_, _) -> false.

single_out_variable(_, _, _, _, {_, none}, _, _, _) -> fail;
single_out_variable(P, N, Pv, Nv, {Singled = {var, SingledName}, neg}, Memo, Fixed, Sym) ->
  case sets:is_element(SingledName, Fixed) of
    true ->
      return_to(P, N, Memo, Fixed, Sym);
    _ ->
      Lneg = fun(ListOfAtoms) -> lists:map(fun stdtypes:tnegate/1, ListOfAtoms) end,
      % k in N' without Delta
      TyConstraint =
        subty:simple_empty(dnf:partitions_to_ty(dnf:simplify(stdtypes:tintersect(P ++ Lneg(N) ++ Pv ++ Lneg([X || X <- Nv, X /= Singled])))), Sym),
      {Singled, TyConstraint, {predef, any}}
  end;
single_out_variable(P, N, Pv, Nv, {Singled = {var, SingledName}, pos}, Memo, Fixed, Sym) ->
  case sets:is_element(SingledName, Fixed) of
    true ->
      return_to(P, N, Memo, Fixed, Sym);
    _ ->
      Lneg = fun(ListOfAtoms) -> lists:map(fun stdtypes:tnegate/1, ListOfAtoms) end,
      % k in P'
      % flip positive into negative and negative into positive
      TyConstraint =
        subty:simple_empty(dnf:partitions_to_ty(dnf:simplify(stdtypes:tunion(Lneg(P) ++ N ++ Lneg([X || X <- Pv, X /= Singled]) ++ Nv))), Sym),
      {Singled, {predef, none}, TyConstraint}
  end.


return_to(P, N, Memo, Fixed, Sym) ->
  Lneg = fun(ListOfAtoms) -> lists:map(fun stdtypes:tnegate/1, ListOfAtoms) end,
  TyConstraint = stdtypes:tintersect(P ++ Lneg(N)),
  {delta, norm_and_merge(TyConstraint, Memo, Fixed, Sym)}.


saturate([], _Memo, _Fix, _Sym) -> [];
saturate([[]], _Memo, _Fix, _Sym) -> [[]];
saturate(S, Memo, Fix, Sym) ->
  Ls = lists:map(fun(E) ->
    saturate_single(E, [], Memo, Fix, Sym) end, S),
  lists:foldl(fun(E, Acc) ->
    lazy_join(E, Acc, Sym)
              end, [], Ls).


saturate_single([], Pre, _Memo, _Fix, _Sym) -> [Pre];
saturate_single([X = {_Var, {predef, none}, _Tb} | Cs], Pre, Memo, Fix, Sym) -> saturate_single(Cs, Pre ++ [X], Memo, Fix, Sym);
saturate_single([X = {_Var, _Ta, {predef, any}} | Cs], Pre, Memo, Fix, Sym) -> saturate_single(Cs, Pre ++ [X], Memo, Fix, Sym);
saturate_single([X = {_Var, S, T} | Cs], Pre, Memo, Fix, Sym) ->
  SnT = tintersect([S, tnegate(T)]),

  T_partitions = dnf:simplify(subty:simple_empty(SnT, Sym)),

  {_ZeroPartitions, UnknownPartitions} = partition(T_partitions, Memo),

  case UnknownPartitions of
    [] ->
      saturate_single(Cs, Pre ++ [X], Memo, Fix, Sym);
    _ ->
      case norm_partitions(UnknownPartitions, Memo ++ UnknownPartitions, Fix, Sym)of
        [] -> [];
        [[]] -> saturate_single(Cs, Pre ++ [X], Memo, Fix, Sym);
        SatuAll ->
          NewL = Pre ++ [X] ++ Cs,
          MemoP = Memo ++ UnknownPartitions,
          saturate(lazy_meet(SatuAll, [NewL], Sym), MemoP, Fix, Sym)
      end
  end.






