-module(tally).

-export([
  tally/2,
  tally/3,
  is_satisfiable/3,
  is_satisfiable_base/3,
  is_satisfiable_incremental/4
]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-import(stdtypes, [tvar/1]).
-endif.

-export_type([monomorphic_variables/0, base_sat_result/0]).

-type monomorphic_variables() :: sets:set(ast:ty_varname()).
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).
-type constraints_partition() :: #{term() => [{ast:ty(), ast:ty()}]}.
-type base_sat_result() :: {etally:solutions(), etally:monomorphic_variables()}.

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(Constraints), FixedVars, SymTab)]),

    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, _SubtyConstrs, _Maters, _UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    % cleaning is OK, we only care about one solution
    FinalCons = subst:clean_cons(InternalRawConstraints, FixedVars, SymTab),

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    Partitions = [V || {_, V} <- maps:to_list(MM)],
    case Partitions of
        [] -> {true, satisfiable}; % no subtype constraints
        [First | Rest] ->
            % Check satisfiability for each partition
            FirstRes = do_satisfiable(First, MonomorphicTallyVariables),
            lists:foldl(fun(_, {false, _}) -> {false, []};
                           (C, {true, _}) -> do_satisfiable(C, MonomorphicTallyVariables)
                        end, FirstRes, Rest)
    end.

-spec do_satisfiable([{ast:ty(), ast:ty()}], map()) ->
    {false, [{error, string()}]} | {true, term()}.
do_satisfiable(FinalCons, MonomorphicTallyVariables) ->
    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- FinalCons],
    InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),
    case InternalResult of
        false -> {false, []};
        true -> {true, satisfiable}
    end.

% Like is_satisfiable but returns the internal solutions for reuse in incremental checks.
-spec is_satisfiable_base(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, base_sat_result()}.
is_satisfiable_base(SymTab, Constraints, FixedVars) ->
    ty_parser:set_symtab(SymTab),
    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, _SubtyConstrs, _Maters, _UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),
    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),
    % Skip clean_cons and eliminate_hubs here: these transformations can substitute
    % variables that delta constraints (from redundancy checks) still reference.
    % The base solutions must preserve all variable constraints for correct incremental merging.
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, InternalRawConstraints),
    ParsedConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalConstraints = [{L, R} || {L, R} <- ParsedConstraints,
                                     not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),
    case etally:is_tally_satisfiable_with_solutions(InternalConstraints, MonomorphicTallyVariables) of
        false -> {false, []};
        {true, Solutions} -> {true, {Solutions, MonomorphicTallyVariables}}
    end.

% Checks satisfiability incrementally by merging delta constraints into pre-computed base solutions.
-spec is_satisfiable_incremental(symtab:t(), base_sat_result(), constr:collected_constrs(), monomorphic_variables()) ->
    boolean().
is_satisfiable_incremental(SymTab, {BaseSolutions, MonoVars}, DeltaConstrs, _FixedVars) ->
    ty_parser:set_symtab(SymTab),
    Ctx = gradual_utils:new_ctx(),
    {InlinedDelta, _, _, _} = gradual_utils:preprocess_constrs(DeltaConstrs, Ctx),
    DeltaRaw = lists:map(fun ({scsubty, _, S, T}) -> {S, T} end, sets:to_list(InlinedDelta)),
    % Skip clean_cons: delta constraints (after materialization inlining) are between
    % concrete types with no free type variables, so cleaning is a no-op.
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, DeltaRaw),
    ParsedDelta = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalDelta = [{L, R} || {L, R} <- ParsedDelta,
                               not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    etally:is_tally_satisfiable_incremental(InternalDelta, BaseSolutions, MonoVars).

% Check if a constraint T1 <= T2 is trivially true based on syntactic form.
-spec is_trivially_true(ast:ty(), ast:ty()) -> boolean().
is_trivially_true({predef, none}, _) -> true;
is_trivially_true(_, {predef, any}) -> true;
is_trivially_true(_, {predef_alias, term}) -> true;
is_trivially_true(T, T) -> true;
is_trivially_true(_, _) -> false.

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()).

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
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

    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- InternalRawConstraints],

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

    Free = tyutils:free_in_subty_constrs(InlinedConstrs),
    case InternalResult of
        {error, []} -> {error, []};
        _ ->
            % transform to subst:t()
            Sigmas = [subst:mk_tally_subst(
               sets:union(FixedVars, Free),
               maps:from_list([{VarName, ty_parser:unparse(Ty)}
                               || {{var, _, VarName, _}, Ty} <- maps:to_list(Subst)])) % FIXME depends on internal ty_variable representation
             || Subst <- InternalResult],

            lists:map(
              fun({tally_subst, S, Fixed}) ->
                MaterSubst = maps:fold(fun(Var, Ty, MAcc) ->
                    maps:put(Var, subst:apply_base(S, Ty), MAcc)
                  end,
                  #{}, UnificationSubst),
                gradual_utils:postprocess({tally_subst, maps:merge(S, MaterSubst), Fixed}, SubtyConstrs, Maters, SymTab)
              end,
              Sigmas)
      end.

-spec split([{ast:ty(), ast:ty()}], monomorphic_variables()) -> constraints_partition().
split(Constrs, FixedVars) ->
    % Phase 1: Build Union-Find by connecting variables that co-occur in constraints.
    %          Also track constraint index -> variable mapping for grouping.
    {UF, IndexedConstrs, _} = lists:foldl(fun(Entry, {AccUF, AccIdx, I}) ->
        Vars = varset(Entry, FixedVars),
        case Vars of
            [] ->
                % Ground constraint: tag with unique ref so it gets its own group
                {AccUF, [{make_ref(), Entry} | AccIdx], I + 1};
            [First | Rest] ->
                UF1 = uf_ensure(First, AccUF),
                UF2 = lists:foldl(fun(V, U) ->
                    uf_union(First, V, uf_ensure(V, U))
                end, UF1, Rest),
                {UF2, [{First, Entry} | AccIdx], I + 1}
        end
    end, {#{}, [], 0}, Constrs),

    % Phase 2: Group constraints by their root representative.
    lists:foldl(fun({Key, Entry}, Acc) ->
        GroupKey = case is_reference(Key) of
            true -> Key;
            false -> {Root, _} = uf_find(Key, UF), Root
        end,
        maps:update_with(GroupKey, fun(Old) -> [Entry | Old] end, [Entry], Acc)
    end, #{}, IndexedConstrs).

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

%% Union-Find with path compression (functional, returns updated parent map).
-spec uf_ensure(ast:ty_var(), map()) -> map().
uf_ensure(V, Parent) ->
    case maps:is_key(V, Parent) of
        true -> Parent;
        false -> maps:put(V, V, Parent)
    end.

-spec uf_find(ast:ty_var(), map()) -> {ast:ty_var(), map()}.
uf_find(V, Parent) ->
    case maps:get(V, Parent) of
        V -> {V, Parent};
        P ->
            {Root, Parent1} = uf_find(P, Parent),
            {Root, maps:put(V, Root, Parent1)}
    end.

-spec uf_union(ast:ty_var(), ast:ty_var(), map()) -> map().
uf_union(A, B, Parent) ->
    {RootA, Parent1} = uf_find(A, Parent),
    {RootB, Parent2} = uf_find(B, Parent1),
    case RootA =:= RootB of
        true -> Parent2;
        false -> maps:put(RootB, RootA, Parent2)
    end.

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

%% Ground constraints (no free vars) should not merge independent partitions.
%% A ground constraint like {integer(), atom()} has no type variables, so its varset is [].
%% It should go into its own partition, not cause all other partitions to collapse into one.
partition_ground_test() ->
    A = tvar('A'), B = tvar('B'),
    C = tvar('C'), D = tvar('D'),
    Ground1 = {{predef, integer}, {predef, atom}},
    Ground2 = {{predef, float}, {predef, number}},

    % Single ground constraint with variable partitions: should be 3 partitions
    3 = maps:size(split([ {A, B}, Ground1, {C, D} ], sets:new())),
    % Two ground constraints should be 2 separate partitions, not merged into 1
    2 = maps:size(split([ Ground1, Ground2 ], sets:new())),
    % Two ground + two variable partitions = 4 partitions
    4 = maps:size(split([ {A, B}, Ground1, {C, D}, Ground2 ], sets:new())),

    ok.

-endif.
