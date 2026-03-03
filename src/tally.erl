-module(tally).

-export([
  tally/2,
  tally/3,
  tally/4,
  tally/5,
  is_satisfiable/3,
  is_satisfiable/5,
  is_satisfiable_base/3,
  is_satisfiable_base/5,
  is_satisfiable_incremental/4
]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-import(stdtypes, [tvar/1]).
-endif.

-export_type([monomorphic_variables/0, base_sat_result/0]).

-type monomorphic_variables() :: sets:set(ast:ty_varname()).
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).
-type constraints_partition() :: #{[ast:ty_var()] => [{ast:ty(), ast:ty()}]}.
-type base_sat_result() :: {etally:solutions(), etally:monomorphic_variables(), subst:base_subst()}.

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars) ->
    is_satisfiable(SymTab, Constraints, FixedVars, none, "").

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), monomorphic_variables(),
    feature_flags:dump_tally_constraints(), string()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars, DumpMode, FunName) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {_PreT, {InlinedConstrs, _SubtyConstrs, _Maters, _UnificationSubst}} = timer:tc(fun() -> gradual_utils:preprocess_constrs(Constraints, Ctx) end),
    % io:format(user, "[TALLY] preprocess: ~pms, ~p constraints~n", [_PreT div 1000, sets:size(InlinedConstrs)]),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    % cleaning is OK, we only care about one solution
    {_CleanT, CleanedCons} = timer:tc(fun() -> subst:clean_cons(InternalRawConstraints, FixedVars, SymTab) end),
    % io:format(user, "[TALLY] clean_cons: ~pms, ~p -> ~p constraints~n", [_CleanT div 1000, length(InternalRawConstraints), length(CleanedCons)]),

    % Pre-filter trivially satisfiable constraints (none ⊆ T, T ⊆ any, T ⊆ T)
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, CleanedCons),
    % io:format(user, "[TALLY] after trivial filter: ~p constraints~n", [length(TrivFiltered)]),

    % Eliminate hub variables: substitute variables that have pure lower bounds
    % and only appear covariantly elsewhere. Sound for satisfiability checking.
    AfterLB = eliminate_hubs(lower, TrivFiltered, FixedVars),
    FinalCons = eliminate_hubs(upper, AfterLB, FixedVars),

    dump_simplified_constraints(DumpMode, FunName, FinalCons),

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    Partitions = [V || {_, V} <- maps:to_list(MM)],
    % io:format(user, "[TALLY] ~p partitions, sizes: ~p~n", [length(Partitions), [length(P) || P <- Partitions]]),
    case Partitions of
        [] -> {true, satisfiable}; % no subtype constraints
        [First | Rest] ->
            FirstRes = do_satisfiable(First, FixedVars),
            lists:foldl(fun(_, {false, _}) -> {false, []};
                           (C, {true, _}) -> do_satisfiable(C, FixedVars)
                        end, FirstRes, Rest)
    end.

-spec do_satisfiable([{ast:ty(), ast:ty()}], monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
do_satisfiable(FinalCons, FixedVars) ->
    ParsedConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- FinalCons],
    % Pre-filter: if LHS is empty or RHS is any, constraint T1 ⊆ T2 is trivially satisfied.
    InternalConstraints = [{L, R} || {L, R} <- ParsedConstraints,
                                     not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],

    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),
    case InternalResult of
        false -> {false, []};
        true -> {true, satisfiable}
    end.

% Like is_satisfiable but returns the internal solutions for reuse in incremental checks.
-spec is_satisfiable_base(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, base_sat_result()}.
is_satisfiable_base(SymTab, Constraints, FixedVars) ->
    is_satisfiable_base(SymTab, Constraints, FixedVars, none, "").

-spec is_satisfiable_base(symtab:t(), constr:collected_constrs(), monomorphic_variables(),
    feature_flags:dump_tally_constraints(), string()) ->
    {false, [{error, string()}]} | {true, base_sat_result()}.
is_satisfiable_base(SymTab, Constraints, FixedVars, DumpMode, FunName) ->
    is_satisfiable_base(SymTab, Constraints, FixedVars, #{}, DumpMode, FunName).

% Like is_satisfiable_base/3 but accepts an external materialization substitution
% from pre-inlined constraints. Merged into the delta substitution for incremental checks.
-spec is_satisfiable_base(symtab:t(), constr:collected_constrs(), monomorphic_variables(), subst:base_subst(),
    feature_flags:dump_tally_constraints(), string()) ->
    {false, [{error, string()}]} | {true, base_sat_result()}.
is_satisfiable_base(SymTab, Constraints, FixedVars, ExternalMaterSubst, DumpMode, FunName) ->
    ty_parser:set_symtab(SymTab),
    Ctx = gradual_utils:new_ctx(),
    {_, {InlinedConstrs, _, _, MaterSubst}} = timer:tc(fun() -> gradual_utils:preprocess_constrs(Constraints, Ctx) end),
    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),
    % Skip clean_cons here: it replaces variables with any/none based on polarity,
    % which is lossy and could break delta constraint references.
    % Eliminate hub variables: unlike clean_cons, this substitutes variables with their
    % actual bounds (e.g. $0 -> a|b|c), which is lossless.
    TrivFiltered0 = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, InternalRawConstraints),
    {AfterLB, LBSubst} = eliminate_hubs_subst(lower, TrivFiltered0, FixedVars),
    {TrivFiltered, UBSubst} = eliminate_hubs_subst(upper, AfterLB, FixedVars),
    dump_simplified_constraints(DumpMode, FunName, TrivFiltered),
    % Merge all substitutions for delta constraint resolution:
    % ExternalMaterSubst from pre-inlining, MaterSubst from preprocess_constrs,
    % and hub substitutions from eliminate_hubs.
    DeltaSubst = maps:merge(ExternalMaterSubst, maps:merge(MaterSubst, maps:merge(LBSubst, UBSubst))),
    ParsedConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalConstraints = [{L, R} || {L, R} <- ParsedConstraints,
                                     not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),
    case etally:is_tally_satisfiable_with_solutions(InternalConstraints, MonomorphicTallyVariables) of
        false -> {false, []};
        {true, Solutions} -> {true, {Solutions, MonomorphicTallyVariables, DeltaSubst}}
    end.

% Checks satisfiability incrementally by merging delta constraints into pre-computed base solutions.
-spec is_satisfiable_incremental(symtab:t(), base_sat_result(), constr:collected_constrs(), monomorphic_variables()) ->
    boolean().
is_satisfiable_incremental(SymTab, {BaseSolutions, MonoVars, BaseSubst}, DeltaConstrs, _FixedVars) ->
    ty_parser:set_symtab(SymTab),
    Ctx = gradual_utils:new_ctx(),
    {InlinedDelta, _, _, _} = gradual_utils:preprocess_constrs(DeltaConstrs, Ctx),
    DeltaRaw = lists:map(fun ({scsubty, _, S, T}) -> {S, T} end, sets:to_list(InlinedDelta)),
    % Apply base substitution: resolve references to base variables that were
    % eliminated during is_satisfiable_base (via materialization inlining and hub elimination).
    DeltaResolved = [{subst:apply_base(BaseSubst, S), subst:apply_base(BaseSubst, T)} || {S, T} <- DeltaRaw],
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, DeltaResolved),
    ParsedDelta = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalDelta = [{L, R} || {L, R} <- ParsedDelta,
                               not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    etally:is_tally_satisfiable_incremental(InternalDelta, BaseSolutions, MonoVars).

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()). % elp:ignore W0049

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
    tally(SymTab, Constraints, FixedVars, none, "").

-spec tally(symtab:t(), constr:collected_constrs(), feature_flags:dump_tally_constraints(), string()) -> tally_res().
tally(SymTab, Constraints, DumpMode, FunName) ->
    tally(SymTab, Constraints, sets:new(), DumpMode, FunName). % elp:ignore W0049

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname()),
    feature_flags:dump_tally_constraints(), string()) -> tally_res().
tally(SymTab, Constraints, FixedVars, DumpMode, FunName) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, SubtyConstrs, Maters, UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    dump_simplified_constraints(DumpMode, FunName, InternalRawConstraints),

    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- InternalRawConstraints],

    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult =
    % TODO tally should return a nonempty list of solutions if not an error
    case etally:tally(InternalConstraints, MonomorphicTallyVariables) of
        [] -> {error, []};
        Z -> Z
    end,

    Free = tyutils:free_in_subty_constrs(InlinedConstrs),
    process_tally_result(InternalResult, FixedVars, Free, UnificationSubst, SubtyConstrs, Maters, SymTab).

-spec process_tally_result(
    {error, []} | etally:tally_solutions_nonempty(), sets:set(ast:ty_varname()), sets:set(ast:ty_varname()),
    subst:base_subst(), constr:subty_constrs(), constr:mater_constrs(), symtab:t()
) -> tally_res().
process_tally_result({error, []}, _FixedVars, _Free, _UnificationSubst, _SubtyConstrs, _Maters, _SymTab) ->
    {error, []};
process_tally_result(InternalResult, FixedVars, Free, UnificationSubst, SubtyConstrs, Maters, SymTab) ->
    FixedFree = sets:union(FixedVars, Free),
    lists:map(
      fun(Subst) ->
        % elp:ignore W0036 W0034
        TallySubst = subst:mk_tally_subst(
           FixedFree,
           maps:from_list([{VarName, ty_parser:unparse(Ty)}
                           || {{var, _, VarName, _}, Ty} <- maps:to_list(Subst)])), % FIXME depends on internal ty_variable representation
        apply_mater_and_postprocess(TallySubst, UnificationSubst, SubtyConstrs, Maters, SymTab)
      end,
      InternalResult).

% Applies the unification substitution to a tally_subst and runs postprocessing.
-spec apply_mater_and_postprocess(subst:tally_subst(), subst:base_subst(),
    constr:subty_constrs(), constr:mater_constrs(), symtab:t()) -> subst:tally_subst().
apply_mater_and_postprocess({tally_subst, S, Fixed}, UnificationSubst, SubtyConstrs, Maters, SymTab) ->
    MaterSubst = maps:fold(fun(Var, Ty, MAcc) ->
        maps:put(Var, subst:apply_base(S, Ty), MAcc)
      end,
      #{}, UnificationSubst),
    gradual_utils:postprocess({tally_subst, maps:merge(S, MaterSubst), Fixed}, SubtyConstrs, Maters, SymTab).

-spec split([{ast:ty(), ast:ty()}], monomorphic_variables()) -> constraints_partition().
split(Constrs, FixedVars) ->
    lists:foldl(fun(Entry, Acc) ->
        add_to_partition(Entry, varset(Entry, FixedVars), Acc)
    end, #{}, Constrs).

-spec add_to_partition({ast:ty(), ast:ty()}, [ast:ty_var()], constraints_partition()) -> constraints_partition().
add_to_partition(Entry, Vars, Acc) ->
    case find_group(Vars, Acc) of
        {found, SharedVarsL} ->
            merge_groups(Entry, Vars, SharedVarsL, Acc);
        none ->
            maps:put(Vars, [Entry], Acc)
    end.

-spec merge_groups({ast:ty(), ast:ty()}, [ast:ty_var()], [[ast:ty_var()]], constraints_partition()) ->
    constraints_partition().
merge_groups(Entry, Vars, SharedVarsL, Acc) ->
    {NewMap, NewVars, NewValues} = collect_shared(SharedVarsL, Acc, Vars, [Entry]),
    % elp:ignore W0030
    maps:put(NewVars, NewValues, NewMap).

-spec collect_shared([[ast:ty_var()]], constraints_partition(), [ast:ty_var()], [{ast:ty(), ast:ty()}]) ->
    {constraints_partition(), [ast:ty_var()], [{ast:ty(), ast:ty()}]}.
collect_shared([], Map, Vars, Values) ->
    {Map, Vars, Values};
collect_shared([SharedVars | Rest], Map, Vars, Values) ->
    OldEntry = maps:get(SharedVars, Map),
    NewMap = maps:remove(SharedVars, Map),
    collect_shared(Rest, NewMap, uvars(SharedVars, Vars), OldEntry ++ Values).

-spec varset({ast:ty(), ast:ty()}, monomorphic_variables()) -> [ast:ty_var()].
varset(Constraint, FixedVars) ->
    lists:usort(utils:everything(fun
            ({var, N} = Var) when is_atom(N) ->
                                         case sets:is_element(N, FixedVars) of
                                             true -> error;
                                             _ -> {ok, Var}
                                         end;
            (_) -> error
        end, Constraint)).

-spec uvars([ast:ty_var()], [ast:ty_var()]) -> [ast:ty_var()].
uvars(V1, V2) ->
    lists:usort(V1 ++ V2).

-spec find_group([ast:ty_var()], constraints_partition()) -> {found, [[ast:ty_var()]]} | none.
find_group(Vars, MapOfVarsToConstraints) ->
    % elp:ignore W0049
    SV = sets:from_list(Vars),
    lists:foldl(
      fun
          (Current, {found, S}) ->
              % elp:ignore W0049
              CurrentSV = sets:from_list(Current),
              case not (sets:is_empty(SV) andalso sets:is_empty(CurrentSV)) andalso sets:is_disjoint(SV, CurrentSV) of
                  true -> {found, S};
                  false -> {found, [Current | S]}
              end;
          (Current, none) ->
              % elp:ignore W0049
              CurrentSV = sets:from_list(Current),
              case not (sets:is_empty(SV) andalso sets:is_empty(CurrentSV)) andalso sets:is_disjoint(SV, CurrentSV) of
                  true -> none;
                  false -> {found, [Current]}
              end
      end, none, maps:keys(MapOfVarsToConstraints)).

% Apply a substitution to its own values until fixed point.
% Handles chains like $3 ⊆ $1, ($1 ∩ T) ⊆ $0 where $0's value contains $1.
% Self-referential LBs are already excluded by eliminate_hubs, so this terminates.
-spec compose_subst(subst:base_subst()) -> subst:base_subst().
compose_subst(Subst) -> compose_subst(Subst, 10).

-spec compose_subst(subst:base_subst(), non_neg_integer()) -> subst:base_subst().
compose_subst(Subst, 0) -> Subst;
compose_subst(Subst, N) ->
    Composed = maps:map(fun(_V, Ty) -> subst:apply_base(Subst, Ty) end, Subst),
    case Composed =:= Subst of
        true -> Subst;
        false -> compose_subst(Composed, N - 1)
    end.

% Eliminate hub variables for satisfiability checking.
% Mode = lower: eliminate variables with pure lower bounds (T ⊆ V), substitute V = union(LBs)
% Mode = upper: eliminate variables with pure upper bounds (V ⊆ T), substitute V = intersection(UBs)
-spec eliminate_hubs(lower | upper, [{ast:ty(), ast:ty()}], monomorphic_variables()) -> [{ast:ty(), ast:ty()}].
eliminate_hubs(Mode, Constrs, FixedVars) ->
    {Result, _Subst} = eliminate_hubs_subst(Mode, Constrs, FixedVars),
    Result.

% Like eliminate_hubs/3 but also returns the substitution applied to eliminated variables.
-spec eliminate_hubs_subst(lower | upper, [{ast:ty(), ast:ty()}], monomorphic_variables()) ->
    {[{ast:ty(), ast:ty()}], subst:base_subst()}.
eliminate_hubs_subst(Mode, Constrs, FixedVars) ->
    % Step 1: Find pure bound constraints where V is free
    BoundMap = lists:foldl(fun(Constr, Acc) ->
        case bound_var(Mode, Constr) of
            {ok, V, Bound} ->
                case sets:is_element(V, FixedVars) of
                    true -> Acc;
                    false -> maps:update_with(V, fun(Bs) -> [Bound | Bs] end, [Bound], Acc)
                end;
            none -> Acc
        end
    end, #{}, Constrs),

    % Step 2: For each candidate V, verify:
    %   - V doesn't appear inside its own bound values (avoids self-referential substitution)
    %   - V doesn't appear on the "other side" of any non-bound constraint
    Eliminable = maps:filter(fun(V, Bounds) ->
        not lists:any(fun(B) -> var_in_ty(V, B) end, Bounds) andalso
        lists:all(fun(Constr) ->
            case other_side(Mode, Constr) of
                {ok, V2} -> V2 =:= V;
                {check, Ty} -> not var_in_ty(V, Ty)
            end
        end, Constrs)
    end, BoundMap),

    case maps:size(Eliminable) of
        0 -> {Constrs, #{}};
        _ ->
            % Step 3: Build substitution V -> union/intersection(bounds)
            Combiner = case Mode of lower -> union; upper -> intersection end,
            RawSubst = maps:map(fun(_V, Bounds) ->
                case Bounds of
                    [Single] -> Single;
                    Multiple -> {Combiner, Multiple}
                end
            end, Eliminable),
            % Compose: apply the substitution to its own values so that
            % chained eliminations are resolved. Iterate until fixed point.
            Subst = compose_subst(RawSubst),
            EliminatedVarSet = sets:from_list(maps:keys(Eliminable)),

            % Step 4: Apply substitution and remove pure bound constraints for eliminated vars
            Result = lists:filtermap(fun(Constr) ->
                {T1, T2} = Constr,
                case bound_var(Mode, Constr) of
                    {ok, V, _} ->
                        case sets:is_element(V, EliminatedVarSet) of
                            true -> false;
                            false -> subst_constr(Subst, T1, T2)
                        end;
                    none -> subst_constr(Subst, T1, T2)
                end
            end, Constrs),
            {Result, Subst}
    end.

% Extract the bound variable and bound type from a constraint, depending on mode.
% lower: {T, {var, V}} -> V is bounded from below by T
% upper: {{var, V}, T} -> V is bounded from above by T
-spec bound_var(lower | upper, {ast:ty(), ast:ty()}) -> {ok, ast:ty_varname(), ast:ty()} | none.
bound_var(lower, {Bound, {var, V}}) when is_atom(V) -> {ok, V, Bound};
bound_var(upper, {{var, V}, Bound}) when is_atom(V) -> {ok, V, Bound};
bound_var(_, _) -> none.

% For a constraint, return what needs to be checked on the "other side" (the side
% opposite to where the bound variable sits).
% If the bound variable is on this side, return {ok, V} (it's a bound constraint for V).
% Otherwise return {check, Ty} meaning we need to verify V doesn't appear in Ty.
-spec other_side(lower | upper, {ast:ty(), ast:ty()}) -> {ok, ast:ty_varname()} | {check, ast:ty()}.
other_side(lower, {_T1, {var, V}}) when is_atom(V) -> {ok, V};
other_side(lower, {_T1, T2}) -> {check, T2};
other_side(upper, {{var, V}, _T2}) when is_atom(V) -> {ok, V};
other_side(upper, {T1, _T2}) -> {check, T1}.

% Apply substitution to a constraint and filter out trivially true results.
-spec subst_constr(subst:base_subst(), ast:ty(), ast:ty()) -> {true, {ast:ty(), ast:ty()}} | false.
subst_constr(Subst, T1, T2) ->
    ST1 = subst:apply_base(Subst, T1),
    ST2 = subst:apply_base(Subst, T2),
    case is_trivially_true(ST1, ST2) of
        true -> false;
        false -> {true, {ST1, ST2}}
    end.

% Check if a variable name appears anywhere inside a type.
-spec var_in_ty(ast:ty_varname(), ast:ty()) -> boolean().
var_in_ty(VarName, Ty) ->
    lists:any(fun({var, N}) -> N =:= VarName end,
        utils:everything(fun
            ({var, N}) when is_atom(N) -> {ok, {var, N}};
            (_) -> error
        end, Ty)).

% Check if a constraint T1 ⊆ T2 is trivially true based on syntactic form.
-spec is_trivially_true(ast:ty(), ast:ty()) -> boolean().
is_trivially_true({predef, none}, _) -> true;
is_trivially_true(_, {predef, any}) -> true;
is_trivially_true(_, {predef_alias, term}) -> true;
is_trivially_true(T, T) -> true;
is_trivially_true(_, _) -> false.

% % Print a variable co-occurrence graph in DOT format when VAR_GRAPH=1 is set.
% % Nodes are type variables, edges connect variables that appear in the same constraint.
% -spec maybe_print_var_graph([{ast:ty(), ast:ty()}]) -> ok.
% maybe_print_var_graph(Constraints) ->
%     case os:getenv("VAR_GRAPH") of
%         "1" -> print_var_graph(Constraints);
%         _ -> ok
%     end.
%
% -spec print_var_graph([{ast:ty(), ast:ty()}]) -> ok.
% print_var_graph(Constraints) ->
%     GetVar = fun ({var, A}) when is_atom(A) -> {ok, {var, A}}; (_) -> error end,
%     VarGroups = [utils:everything(GetVar, C) || C <- Constraints],
%     Z = fun(A) -> string:replace(atom_to_list(A), "$", "") end,
%     io:format(user, "graph{~n", []),
%     lists:foreach(fun
%         ([]) -> ok;
%         ([_]) -> ok;
%         (All) ->
%             [io:format(user, "  ~s -- ~s~n", [Z(R), Z(R2)])
%              || {var, R} <- All, {var, R2} <- All, R /= R2]
%     end, VarGroups),
%     io:format(user, "}~n", []),
%     ok.

-ifdef(TEST).

partition_test() ->
    A = tvar('A'), B = tvar('B'),
    C = tvar('C'), D = tvar('D'),
    E = tvar('E'), F = tvar('F'),

    2 = maps:size(split([ {A, B}, {C, D} ], sets:new())),
    3 = maps:size(split([ {A, B}, {C, D}, {E, F} ], sets:new())),
    2 = maps:size(split([ {A, B}, {B, C}, {D, D} ], sets:new())),
    1 = maps:size(split([ {A, B}, {B, C}, {C, D}, {D, A} ], sets:new())),
    2 = maps:size(split([ {A, B}, {B, C}, {C, D}, {D, A} ], sets:from_list(['D', 'A']))),

    ok.

-endif.

% Dump simplified constraints (right before etally) to stdout when mode matches.
-spec dump_simplified_constraints(feature_flags:dump_tally_constraints(), string(), [{ast:ty(), ast:ty()}]) -> ok.
dump_simplified_constraints(simplified, FunName, Constraints) ->
    Rendered = string:join(
        [utils:sformat("  ~s <: ~s", pretty:render_ty(T1), pretty:render_ty(T2)) || {T1, T2} <- Constraints],
        "\n"),
    io:format(user, "[simplified] simplified constraints for ~s:~n~s~n", [FunName, Rendered]);
dump_simplified_constraints(_, _, _) -> ok.
