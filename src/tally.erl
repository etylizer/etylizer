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
-type base_sat_result() :: {etally:solutions(), etally:monomorphic_variables(), subst:base_subst()}.

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, Constraints, FixedVars) ->
    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    Ctx = gradual_utils:new_ctx(),
    {InlinedConstrs, _SubtyConstrs, _Maters, _UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),

    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),

    is_satisfiable_internal(SymTab, InternalRawConstraints, FixedVars).

-spec is_satisfiable_internal(symtab:t(), [{ast:ty(), ast:ty()}], monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable_internal(SymTab, InternalRawConstraints, FixedVars) ->
    % Pre-filter trivially satisfiable constraints before cleaning, so that
    % variables appearing only in trivial constraints (e.g. $1 <: any()) don't
    % pollute the polarity analysis and prevent cleaning of other occurrences.
    PreFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, InternalRawConstraints),

    % Check if there are enough free variables and constraints to justify
    % the expensive unfold_ty calls in clean_cons/eliminate_hubs.
    HasFreeVars = lists:any(fun({S, T}) ->
        has_free_var(S, FixedVars) orelse has_free_var(T, FixedVars)
    end, PreFiltered),
    FinalCons = case HasFreeVars andalso length(PreFiltered) >= 2 of
        false -> PreFiltered;
        true -> optimize_constraints(SymTab, PreFiltered, FixedVars)
    end,

    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    Partitions = [V || {_, V} <- maps:to_list(MM)],
    case Partitions of
        [] -> {true, satisfiable}; % no subtype constraints
        [First | Rest] ->
            FirstRes = do_satisfiable(First, MonomorphicTallyVariables),
            lists:foldl(fun(_, {false, _}) -> {false, []};
                           (C, {true, _}) -> do_satisfiable(C, MonomorphicTallyVariables)
                        end, FirstRes, Rest)
    end.

% Apply clean_cons and eliminate_hubs in a fixpoint loop.
-spec optimize_constraints(symtab:t(), [{ast:ty(), ast:ty()}], monomorphic_variables()) -> [{ast:ty(), ast:ty()}].
optimize_constraints(SymTab, Constraints, FixedVars) ->
    CleanedCons = subst:clean_cons(Constraints, FixedVars, SymTab),
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, CleanedCons),
    AfterLB = eliminate_hubs(lower, TrivFiltered, FixedVars, SymTab),
    FinalCons = eliminate_hubs(upper, AfterLB, FixedVars, SymTab),
    case subst:clean_cons(FinalCons, FixedVars, SymTab) of
        FinalCons -> FinalCons;
        NewCons ->
            ReFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, NewCons),
            optimize_constraints(SymTab, ReFiltered, FixedVars)
    end.

% Check if a type contains any free (non-fixed) type variable.
-spec has_free_var(ast:ty(), sets:set(ast:ty_varname())) -> boolean().
has_free_var({var, V}, Fixed) -> not sets:is_element(V, Fixed);
has_free_var(T, Fixed) when is_tuple(T) ->
    has_free_var_list(tuple_to_list(T), Fixed);
has_free_var(T, Fixed) when is_list(T) ->
    has_free_var_list(T, Fixed);
has_free_var(_, _) -> false.

-spec has_free_var_list([term()], sets:set(ast:ty_varname())) -> boolean().
has_free_var_list([], _) -> false;
has_free_var_list([H | T], Fixed) ->
    has_free_var(H, Fixed) orelse has_free_var_list(T, Fixed).

-spec do_satisfiable([{ast:ty(), ast:ty()}], map()) ->
    {false, [{error, string()}]} | {true, term()}.
do_satisfiable(FinalCons, MonomorphicTallyVariables) ->
    ParsedConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- FinalCons],
    InternalConstraints = [{L, R} || {L, R} <- ParsedConstraints,
                                     not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
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
    {InlinedConstrs, _, _, UnificationSubst} = gradual_utils:preprocess_constrs(Constraints, Ctx),
    InternalRawConstraints =
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) ->
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end,
                           sets:to_list(InlinedConstrs))),
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, InternalRawConstraints),
    ParsedConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalConstraints = [{L, R} || {L, R} <- ParsedConstraints,
                                     not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),
    case etally:is_tally_satisfiable_with_solutions(InternalConstraints, MonomorphicTallyVariables) of
        false -> {false, []};
        {true, Solutions} -> {true, {Solutions, MonomorphicTallyVariables, UnificationSubst}}
    end.

% Checks satisfiability incrementally by merging delta constraints into pre-computed base solutions.
-spec is_satisfiable_incremental(symtab:t(), base_sat_result(), constr:collected_constrs(), monomorphic_variables()) ->
    boolean().
is_satisfiable_incremental(SymTab, {BaseSolutions, MonoVars, BaseSubst}, DeltaConstrs, _FixedVars) ->
    ty_parser:set_symtab(SymTab),
    Ctx = gradual_utils:new_ctx(),
    {InlinedDelta, _, _, _} = gradual_utils:preprocess_constrs(DeltaConstrs, Ctx),
    DeltaRaw = lists:map(fun ({scsubty, _, S, T}) ->
        {subst:apply_base(BaseSubst, S), subst:apply_base(BaseSubst, T)}
    end, sets:to_list(InlinedDelta)),
    TrivFiltered = lists:filter(fun({T1, T2}) -> not is_trivially_true(T1, T2) end, DeltaRaw),
    ParsedDelta = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- TrivFiltered],
    InternalDelta = [{L, R} || {L, R} <- ParsedDelta,
                               not ty_node:is_empty(L), not ty_node:leq(ty_node:any(), R)],
    etally:is_tally_satisfiable_incremental(InternalDelta, BaseSolutions, MonoVars).

-spec tally(symtab:t(), constr:collected_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()).

-spec tally(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, Constraints, FixedVars) ->
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
            Sigmas = [subst:mk_tally_subst(
               sets:union(FixedVars, Free),
               maps:from_list([{VarName, ty_parser:unparse(Ty)}
                               || {{var, _, VarName, _}, Ty} <- maps:to_list(Subst)]))
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
    {UF, IndexedConstrs, _} = lists:foldl(fun(Entry, {AccUF, AccIdx, I}) ->
        Vars = varset(Entry, FixedVars),
        case Vars of
            [] ->
                {AccUF, [{make_ref(), Entry} | AccIdx], I + 1};
            [First | Rest] ->
                UF1 = uf_ensure(First, AccUF),
                UF2 = lists:foldl(fun(V, U) ->
                    uf_union(First, V, uf_ensure(V, U))
                end, UF1, Rest),
                {UF2, [{First, Entry} | AccIdx], I + 1}
        end
    end, {#{}, [], 0}, Constrs),

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

% Apply a substitution to its own values until fixed point.
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
-spec eliminate_hubs(lower | upper, [{ast:ty(), ast:ty()}], monomorphic_variables(), symtab:t()) -> [{ast:ty(), ast:ty()}].
eliminate_hubs(Mode, Constrs, FixedVars, SymTab) ->
    {Result, _Subst} = eliminate_hubs_subst(Mode, Constrs, FixedVars, SymTab),
    Result.

% Like eliminate_hubs/4 but also returns the substitution.
-spec eliminate_hubs_subst(lower | upper, [{ast:ty(), ast:ty()}], monomorphic_variables(), symtab:t()) ->
    {[{ast:ty(), ast:ty()}], subst:base_subst()}.
eliminate_hubs_subst(Mode, Constrs, FixedVars, SymTab) ->
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

    BadPos = case Mode of lower -> 1; upper -> 0 end,
    Unfold = fun(Ty) -> ast_utils:unfold_ty(SymTab, Ty) end,
    TaggedConstrs = [{bound_var(Mode, C), {Unfold(C1), Unfold(C2)}} || C = {C1, C2} <- Constrs],
    Eliminable = maps:filter(fun(V, Bounds) ->
        not lists:any(fun(B) -> var_in_ty(V, B) end, Bounds) andalso
        begin
            NonBoundConstrs = [UC || {Tag, UC} <- TaggedConstrs,
                                     case Tag of {ok, V2, _} -> V2 =/= V; none -> true end],
            VarPols = subst:collect_vars_clist(NonBoundConstrs, 0, #{}, sets:new()),
            case maps:find(V, VarPols) of
                {ok, Positions} -> not lists:member(BadPos, Positions);
                error -> true
            end
        end
    end, BoundMap),

    case maps:size(Eliminable) of
        0 -> {Constrs, #{}};
        _ ->
            Combiner = case Mode of lower -> union; upper -> intersection end,
            RawSubst = maps:map(fun(_V, Bounds) ->
                case Bounds of
                    [Single] -> Single;
                    Multiple -> {Combiner, Multiple}
                end
            end, Eliminable),
            Subst = compose_subst(RawSubst),
            EliminatedVarSet = sets:from_list(maps:keys(Eliminable)),

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

-spec bound_var(lower | upper, {ast:ty(), ast:ty()}) -> {ok, ast:ty_varname(), ast:ty()} | none.
bound_var(lower, {Bound, {var, V}}) when is_atom(V) -> {ok, V, Bound};
bound_var(upper, {{var, V}, Bound}) when is_atom(V) -> {ok, V, Bound};
bound_var(_, _) -> none.

-spec subst_constr(subst:base_subst(), ast:ty(), ast:ty()) -> {true, {ast:ty(), ast:ty()}} | false.
subst_constr(Subst, T1, T2) ->
    ST1 = subst:apply_base(Subst, T1),
    ST2 = subst:apply_base(Subst, T2),
    case is_trivially_true(ST1, ST2) of
        true -> false;
        false -> {true, {ST1, ST2}}
    end.

-spec var_in_ty(ast:ty_varname(), ast:ty()) -> boolean().
var_in_ty(VarName, Ty) ->
    lists:any(fun({var, N}) -> N =:= VarName end,
        utils:everything(fun
            ({var, N}) when is_atom(N) -> {ok, {var, N}};
            (_) -> error
        end, Ty)).

-spec is_trivially_true(ast:ty(), ast:ty()) -> boolean().
is_trivially_true({predef, none}, _) -> true;
is_trivially_true(_, {predef, any}) -> true;
is_trivially_true(_, {predef_alias, term}) -> true;
is_trivially_true(T, T) -> true;
is_trivially_true({intersection, Ts}, T2) ->
    lists:any(fun(T) -> is_trivially_true(T, T2) end, Ts);
is_trivially_true(T1, {union, Ts}) ->
    lists:any(fun(T) -> is_trivially_true(T1, T) end, Ts);
is_trivially_true(_, _) -> false.

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

partition_ground_test() ->
    A = tvar('A'), B = tvar('B'),
    C = tvar('C'), D = tvar('D'),
    Ground1 = {{predef, integer}, {predef, atom}},
    Ground2 = {{predef, float}, {predef, number}},

    3 = maps:size(split([ {A, B}, Ground1, {C, D} ], sets:new())),
    2 = maps:size(split([ Ground1, Ground2 ], sets:new())),
    4 = maps:size(split([ {A, B}, Ground1, {C, D}, Ground2 ], sets:new())),

    ok.

-endif.
