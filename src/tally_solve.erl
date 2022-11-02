-module(tally_solve).

%% API
-export([solve/3]).

-import(stdtypes, [tintersect/1, tunion/1, tvar/1]).

solve(E = {fail, _}, _, _) -> E;
solve(M, Fix, SymTab) ->

  logger:debug("Solving ~p", [M]),
  S = ([ solve_single(C, [], Fix, SymTab) || C <- M]),

%%  logger:notice("Unifying ~p", [S]),

  RawSubstitutions = [unify(E) || E <- S],

  logger:debug("Cleaning ~p", [RawSubstitutions]),

  % unify produces very ugly types
  % clean up a bit
  CleanSubstitution = fun(Substitution, CFix) ->
    CleanedList = lists:map(fun({Var, Ty}) ->
      {Var, clean_type(Ty, CFix, SymTab)} end, Substitution),
    CleanedList
                      end,

  lists:map(fun(E) -> CleanSubstitution(E, Fix) end, RawSubstitutions).


solve_single([], Equations, _, _SymTab) -> Equations;
solve_single([{SmallestVar, Left, Right} | Cons], Equations, Fix, SymTab) ->
  % constraints are already sorted by variable ordering
  % smallest variable first
  logger:debug("Solving lower and upper bounds of ~p", [SmallestVar]),

  FreshVar = fresh_variable_bigger_order(SmallestVar),
  % FIXME ok this is the payment for using implicit Erlang ordering
  true = (FreshVar > SmallestVar), % sanity

  NewEq = Equations ++ [{eq, SmallestVar, tintersect([tunion([Left, FreshVar]), Right])}],

  solve_single(Cons, NewEq, Fix, SymTab).

fresh_variable_bigger_order({Type, VariableName}) ->
  Uniq = erlang:unique_integer(),
  ToName = lists:takewhile(fun(E) -> not(E == $-) end, atom_to_list(VariableName)),

  New = {Type,
    %% behold the universally feared dynamically created Erlang atom
    list_to_atom(
      ToName ++ erlang:integer_to_list(Uniq)
    )
  },

  New.


unify([]) -> [];
unify(EquationList) ->
  [Eq = {eq, {var, AName}, TA} | _Tail] = lists:usort(EquationList),

  % tα {X/α}
  FreshVar = {var, list_to_atom( "XMu" ++ erlang:integer_to_list(erlang:unique_integer()) ) },
  Mapping = #{AName => FreshVar},
  Inner = subst:apply(Mapping, TA),
  NewTA = case contains_variable({var, AName}, TA) of
            true -> stdtypes:tmu(FreshVar, Inner);
            false -> TA
          end,

  Mapping2 = #{AName => NewTA},
  E_ = [
    {eq, XA, subst:apply(Mapping2, TAA)} ||
    (X = {eq, XA, TAA}) <- EquationList, X /= Eq
  ],

  Sigma = unify(E_),
  NewTASigma = apply_substitution(NewTA, Sigma),

  [{{var, AName}, NewTASigma}] ++ Sigma.

apply_substitution(Ty, Substitutions) ->
  SubstFun = fun({{var, From}, To}, Tyy) ->
    Mapping = #{From => To},
    subst:apply(Mapping, Tyy)
    end,
  lists:foldl(SubstFun, Ty, Substitutions).

clean_type(Ty, Fix, Sym) ->
  %% collect ALL vars in all positions
  %% if a var is only in co variant position, replace with 0
  %% if a var is only in contra variant position, replace with 1
  VarPositions = collect_vars(Ty, 0, #{}, Fix),

  NoVarsDnf = maps:fold(
    fun(VariableName, VariablePositions, Tyy) ->
      case lists:usort(VariablePositions) of
        [0] ->
          R = subst:apply(#{VariableName => {predef, none}}, Tyy),
          R;
        [1] ->
          subst:apply(#{VariableName => {predef, any}}, Tyy)
      end
    end, Ty, VarPositions),

  Cleaned = subty:simple_empty(dnf:partitions_to_ty(dnf:simplify(NoVarsDnf)), Sym),

%%%%  Minified = eminify:simplify_minify(NoVarsDnf, SymTab),
%%%%  logger:notice("MINIFIED ~p" , [Minified]),
%%
%%
%%%%  Filtered = lists:filter(fun(Intersection) ->
%%%%    Empty = esubrel:is_subtype_b(SymTab, sets:new(), Intersection, east:empty()),
%%%%    not Empty
%%%%                          end, Intersections),
  Cleaned.


combine_vars(_K, V1, V2) ->
  V1 ++ V2.

%%collect_vars({fun_full, Components, B}, CPos, Pos) ->
%%  M1 = collect_vars(A, 1 - CPos, Pos), % contra variant position
%%  M2 = collect_vars(B, CPos, Pos),
%%  maps:merge_with(fun combine_vars/3, M1, M2);
%%collect_vars({_, product, A, B}, CPos, Pos) ->
%%  M1 = collect_vars(A, CPos, Pos),
%%  M2 = collect_vars(B, CPos, Pos),
%%  maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({K, Components}, CPos, Pos, Fix) when K == union; K == intersection; K == tuple ->
  VPos = lists:map(fun(Ty) -> collect_vars(Ty, CPos, Pos, Fix) end, Components),
  lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, #{}, VPos);
collect_vars({fun_full, Components, Target}, CPos, Pos, Fix) ->
  VPos = lists:map(fun(Ty) -> collect_vars(Ty, CPos, Pos, Fix) end, Components),
  M1 = lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, #{}, VPos),
  M2 = collect_vars(Target, CPos, Pos, Fix),
  maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({negation, Ty}, CPos, Pos, Fix) -> collect_vars(Ty, CPos, Pos, Fix);
collect_vars({predef, _}, _CPos, Pos, _) -> Pos;
collect_vars({predef_alias, _}, _CPos, Pos, _) -> Pos;
collect_vars({singleton, _}, _CPos, Pos, _) -> Pos;
collect_vars({range, _, _}, _CPos, Pos, _) -> Pos;
collect_vars({_, any}, _CPos, Pos, _) -> Pos;
collect_vars({empty_list}, _CPos, Pos, _) -> Pos;
collect_vars({list, A}, CPos, Pos, Fix) ->
  collect_vars(A, CPos, Pos, Fix);
collect_vars({improper_list, A, B}, CPos, Pos, Fix) ->
  M1 = collect_vars(A, CPos, Pos, Fix),
  M2 = collect_vars(B, CPos, Pos, Fix),
  maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({var, Name}, CPos, Pos, Fix) ->
  case sets:is_element(Name, Fix) of
    true -> Pos;
    _ ->
      AllPositions = maps:get(Name, Pos, []),
      Pos#{Name => AllPositions ++ [CPos]}
  end;
collect_vars(Ty, _, _, _) ->
  logger:error("Unhandled collect vars branch: ~p", [Ty]),
  throw({todo_collect_vars, Ty}).

contains_variable(_, {_, any}) -> false;
contains_variable({var, A}, {var, A}) -> true;
contains_variable(_, {T, _}) when T == var; T == singleton -> false;
contains_variable(V, {Type, A}) when Type == negation -> contains_variable(V, A);
contains_variable(V, {Type, A}) when Type == union; Type == intersection; Type == tuple ->
  lists:foldl(fun(Ty, R) -> R orelse contains_variable(V, Ty) end, false, A);
contains_variable(V, {mu, Var, InnerType}) ->
  contains_variable(V, Var) orelse contains_variable(V, InnerType);
contains_variable(_, {range, _, _}) -> false;
contains_variable(_, {predef, _}) -> false;
contains_variable(_, {predef_alias, _}) -> false;
contains_variable(_, {empty_list}) -> false;
contains_variable(V, {fun_full, C, T}) ->
  lists:foldl(fun(Ty, R) -> R orelse contains_variable(V, Ty) end, false, C) orelse contains_variable(V, T);
contains_variable(V, {list, A}) ->
  contains_variable(V, A);
contains_variable(V, {improper_list, A, B}) ->
  contains_variable(V, A) orelse contains_variable(V, B);
contains_variable(_, Type) ->
  logger:error("Unhandled contains branch: ~p", [Type]),
  throw(todo).

