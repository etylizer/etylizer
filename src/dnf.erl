-module(dnf).

-export([to_dnf/1, to_nnf/1
%simplify/1, 
%partitions_to_ty/1, 
%filter_empty_intersections/1
]).

%% ============
%% NNF
%% ============

-spec to_nnf(ast:ty()) -> ast:ty().
to_nnf({negation, {negation, A}}) ->
  to_nnf(A);
to_nnf({negation, {union, Components}}) ->
  {intersection, lists:map(fun (E) -> to_nnf({negation, E}) end, Components)};
to_nnf({negation, {intersection, Components}}) ->
  {union, lists:map(fun (E) -> to_nnf({negation, E}) end, Components)};
to_nnf({intersection, Components}) ->
  {intersection, lists:map(fun (E) -> to_nnf(E) end, Components)};
to_nnf({union, Components}) ->
  {union, lists:map(fun (E) -> to_nnf(E) end, Components)};
to_nnf(A) -> A.

%% ============
%% DNF
%% ============

-spec to_dnf(ast:ty()) -> {union, [{intersection, [ast:ty()]}]}. %% ast:ty() \ (ast:ty_union() U ast:ty_intersection)
to_dnf({union, []}) -> {union, []}; % empty
to_dnf({union, Components}) ->
  Dnfs  = lists:flatten(
    lists:map(
      fun (C) -> {union, Inner} = to_dnf(C), Inner end,
      Components)
  ),
  {union, Dnfs};
to_dnf({intersection, []}) -> {union, [{intersection, []}]}; % any
to_dnf({intersection, Components}) ->
  [First | Tail] = lists:map(fun (C) -> Inner = to_dnf(C), Inner end, Components),
  lists:foldl(fun({union, AllIa}, {union, AllIb}) ->
    {union, [ {intersection, Ai ++ Bi} || {intersection, Ai} <- AllIa, {intersection, Bi} <- AllIb]}
              end, First, Tail);
to_dnf(A) ->
  {union, [{intersection, [A]}]}.


simplify(Ty) ->
  {union, RawLines} =
    filter_empty_intersections(to_dnf(to_nnf(unfold_predef_alias(Ty)))),
  {union, Lines} = filter_structural_subsets(RawLines),
  Partitioned = lists:map(fun partition_intersection/1, Lines),
  Simplified = lists:usort(lists:filter(fun(empty) -> false;(_) -> true end ,lists:map(fun simplify_line/1, Partitioned))),

  Simplified.

partitions_to_ty([]) -> {predef, none};
partitions_to_ty([{{P, Pv}, {N, Nv}}]) ->
  All = P ++ Pv ++ lists:map(fun stdtypes:tnegate/1, N) ++ lists:map(fun stdtypes:tnegate/1, Nv),
  case All of
    [] -> {predef, any};
    [X] -> X;
    _ -> stdtypes:tintersect(All)
  end;
partitions_to_ty(All) ->
  ToUnion = lists:map(fun(P) -> partitions_to_ty([P]) end, All),
  case ToUnion of
    [] -> {predef, none};
    [X] -> X;
    _ -> stdtypes:tunion(ToUnion)
  end.




partition_intersection({intersection, Components}) ->
  {
    {[ez(C) || C <- Components, is_pos(C), not is_var(C)], [C || C <- Components, is_pos(C), is_var(C)]},
    {[ez(C) || {negation, C} <- Components, not is_var(C)], [C || {negation, C} <- Components, is_var(C)]}
  }.

ez({tuple, C}) ->
  {tuple, lists:map(fun(E) -> partitions_to_ty(simplify(E)) end, C)};
ez({fun_full, C, T}) ->
  {fun_full,
    lists:map(fun(E) -> partitions_to_ty(simplify(E)) end, C),
    partitions_to_ty(simplify(T))
    };
ez({improper_list, A, B}) ->
  {improper_list,
    partitions_to_ty(simplify(A)),
    partitions_to_ty(simplify(B))
  };
ez(Ty) -> Ty.


simplify_line(_CoClause = {{P, Pv}, {N, Nv}}) ->
  Counters = #{},

  NewCounters = lists:foldl(
    fun
      (_, empty) -> empty;
      (Atom, M) ->
        Mp = maps:put(type_of(Atom), 1, M),
        case maps:size(Mp) > 1 of
          true -> empty;
          _ -> Mp
        end
    end, Counters, P),

  case NewCounters of
    empty -> empty;
    _ ->
%%      CoClause
      case lists:any(fun(E) -> E end, [lists:member(X, Nv) || X <- Pv]) of
        true -> empty;
        _ ->

          case lists:any(fun(E) -> E end, [lists:member(X, N) || X <- P]) of
            true -> empty;
            _ -> normalize_kinds({{P, Pv}, {filter_other_kinds(N, NewCounters), Nv}})
          end
      end
  end.

normalize_kinds(All = {{Lists = [X | _Other], Pv}, {N, Nv}}) ->
  case type_of(X) of
    list -> {{[normalize_list(Lists)], Pv}, {N, Nv}};
    _ -> All
  end;
normalize_kinds(X) -> X.


normalize_list(AllLists) ->
  lists:foldl(
    fun({improper_list, A, B}, {improper_list, S, T}) ->
      {improper_list,
        partitions_to_ty(simplify(ast_lib:mk_intersection([A, S]))),
        partitions_to_ty(simplify(ast_lib:mk_intersection([B, T])))
      }
    end,
    {improper_list, stdtypes:any(), stdtypes:any()},
    AllLists
  ).



filter_other_kinds([], _TypeMap) -> [];
filter_other_kinds(N, TypeMap) ->
  case maps:to_list(TypeMap) of
    [{Type, _}] ->
      maps:to_list(TypeMap),
      [X || X <- N, type_of(X) == Type];
    _ -> N
  end.

filter_structural_subsets(Lines) ->
  TODO = [gb_sets:from_list(Parts) || {intersection, Parts} <- Lines],

  HasSmaller = fun(IntersectionSet, Others) ->
    lists:any(fun(OtherSet) ->
      gb_sets:is_subset(OtherSet, IntersectionSet) end, Others)
    end,

  R = lists:foldl(fun(Intersection, AllLines) ->
    Smaller = HasSmaller(Intersection, lists:delete(Intersection, AllLines)),
    case Smaller of
      true ->
        lists:delete(Intersection, AllLines);
      _ ->
        AllLines
    end
                  end, TODO, TODO),

  Fin = [{intersection, gb_sets:to_list(Parts)} || Parts <- R],
  {union, Fin}.





type_of({tuple, C}) -> {tuple, length(C)};
type_of({fun_full, C, _T}) -> {fun_full, length(C)};

type_of({singleton, Atom}) when is_atom(Atom) -> atom;
type_of({predef, atom}) -> atom;

type_of({predef, reference}) -> special;
type_of({predef, port}) -> special;
type_of({predef, pid}) -> special;
type_of({predef, float}) -> special;
type_of({empty_list}) -> special;

type_of({predef, integer}) -> int;
type_of({singleton, I}) when is_integer(I) -> int;
type_of({range, _, _}) -> int;
type_of({improper_list, _, _}) -> list;
type_of(A) ->
  logger:error("TODO type ~p", [A]),
  throw(todo).



filter_empty_intersections({intersection, Components}) ->
  {intersection,
    lists:usort(lists:filter(fun
                               ({predef, any}) -> false;
                               ({negation, {predef, none}}) -> false;
                               (_) -> true
                             end, Components))};
filter_empty_intersections({union, Intersections}) ->
  NoEmpty =
    lists:filter(fun({intersection, Clause}) ->
      not (lists:member({predef, none}, Clause) orelse lists:member({negation, {predef, any}}, Clause))
                 end, Intersections),

  NoAny = lists:map(fun filter_empty_intersections/1, NoEmpty),

  {union, NoAny}.

is_neg({negation, _}) -> true;
is_neg(_) -> false.
is_pos(Clause) -> not(is_neg(Clause)).
is_var({var, _}) -> true;
is_var({negation, {type_var, _}}) -> true;
is_var(_) -> false.


unfold_predef_alias({list, Ty}) ->
  Ex = unfold_predef_alias(Ty),
  stdtypes:tunion([
    {improper_list, Ex, {empty_list}},
    {empty_list}
  ]);
unfold_predef_alias({predef_alias, Alias}) ->
  unfold_predef_alias(stdtypes:expand_predef_alias(Alias));
unfold_predef_alias({negation, A}) ->
  {negation, unfold_predef_alias(A)};
unfold_predef_alias({intersection, Components}) ->
  {intersection, lists:map(fun (E) -> unfold_predef_alias(E) end, Components)};
unfold_predef_alias({union, Components}) ->
  {union, lists:map(fun (E) -> unfold_predef_alias(E) end, Components)};
unfold_predef_alias(Ty) ->
  Ty.

