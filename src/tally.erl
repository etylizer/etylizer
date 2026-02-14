-module(tally).

-export([
  tally/2,
  tally/3,
  is_satisfiable/3
]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-import(stdtypes, [tvar/1]).
-endif.

-export_type([monomorphic_variables/0]).

-type monomorphic_variables() :: sets:set(ast:ty_varname()).
-type tally_res() :: {error, [{error, string()}]} | nonempty_list(subst:t()).
-type constraints_partition() :: #{[ast:ty_var()] => [{ast:ty(), ast:ty()}]}.

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

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    Partitions = [V || {_, V} <- maps:to_list(MM)],
    case Partitions of
        [] -> {true, satisfiable}; % no subtype constraints
        [First | Rest] ->
            % Check satisfiability for each partition
            FirstRes = do_satisfiable(First, FixedVars),
            lists:foldl(fun(_, {false, _}) -> {false, []};
                           (C, {true, _}) -> do_satisfiable(C, FixedVars)
                        end, FirstRes, Rest)
    end.

-spec do_satisfiable([{ast:ty(), ast:ty()}], monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
do_satisfiable(FinalCons, FixedVars) ->
    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- FinalCons],

    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult = etally:is_tally_satisfiable(InternalConstraints, MonomorphicTallyVariables),
    case InternalResult of
        false -> {false, []};
        true -> {true, satisfiable}
    end.

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()). % elp:ignore W0049

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
