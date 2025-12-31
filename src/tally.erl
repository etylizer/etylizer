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

-spec is_satisfiable(symtab:t(), constr:subty_constrs(), monomorphic_variables()) ->
    {false, [{error, string()}]} | {true, term()}.
is_satisfiable(SymTab, RawConstraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(RawConstraints), FixedVars, SymTab)]),
  
    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    InternalRawConstraints = 
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end, 
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) -> 
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end, 
                           sets:to_list(RawConstraints))),

    % cleaning is OK, we only care about one solution
    FinalCons = subst:clean_cons(InternalRawConstraints, FixedVars, SymTab),

    % Split constraints into independent partitions
    MM = split(FinalCons, FixedVars),
    % elp:ignore W0034
    [First | Rest] = [V || {_, V} <- maps:to_list(MM)],

    % Check satisfiability for each partition
    FirstRes = do_satisfiable(First, FixedVars),
    lists:foldl(fun(_, {false, _}) -> {false, []}; 
                   (C, {true, _}) -> do_satisfiable(C, FixedVars) 
                end, FirstRes, Rest).

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


-spec tally(symtab:t(), constr:subty_constrs()) -> tally_res().
tally(SymTab, Constraints) -> tally(SymTab, Constraints, sets:new()). % elp:ignore W0049

-spec tally(symtab:t(), constr:subty_constrs(), sets:set(ast:ty_varname())) -> tally_res().
tally(SymTab, RawConstraints, FixedVars) ->
    % uncomment to extract a tally test case config file
    % io:format(user, "~s~n", [utils:format_tally_config(sets:to_list(RawConstraints), FixedVars, SymTab)]),
 
    % erlang_types has a global symtab
    ty_parser:set_symtab(SymTab),

    InternalRawConstraints = 
    lists:map( fun ({scsubty, _, S, T}) -> {S, T} end,
               lists:sort( fun ({scsubty, _, S, T}, {scsubty, _, X, Y}) -> 
                                   (erts_debug:size({S, T})) < erts_debug:size(({X, Y})) end, 
                           sets:to_list(RawConstraints))),

    InternalConstraints = [{ty_parser:parse(T1), ty_parser:parse(T2)} || {T1, T2} <- InternalRawConstraints],

    % elp:ignore W0036
    MonomorphicTallyVariables = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- sets:to_list(FixedVars)]),

    InternalResult = etally:tally(InternalConstraints, MonomorphicTallyVariables),

    Free = tyutils:free_in_subty_constrs(RawConstraints),
    case InternalResult of 
        {error, []} -> {error, []}; 
        _ -> % transform to subst:t() 
            [subst:mk_tally_subst( 
               sets:union(FixedVars, Free), 
                % elp:ignore W0036 W0034
               maps:from_list([{VarName, ty_parser:unparse(Ty)} 
                               || {{var, _, VarName}, Ty} <- maps:to_list(Subst)])) 
             || Subst <- InternalResult]
      end.

-spec split([{ast:ty(), ast:ty()}], monomorphic_variables()) -> constraints_partition().
split(Constrs, FixedVars) ->
    lists:foldl(fun(Entry, Acc) ->
        Vars = varset(Entry, FixedVars),
        
        case find_group(Vars, Acc) of
            {found, SharedVarsL} ->
                {NewMap, NewVars, NewValues} = lists:foldl(fun(SharedVars, {CurrentRmMap, CurrentUnionOfVars, CurrentValueMapping}) -> 
                    OldEntry = maps:get(SharedVars, CurrentRmMap),
                    RmMap = maps:remove(SharedVars, CurrentRmMap),
                    {RmMap, uvars(SharedVars, CurrentUnionOfVars), OldEntry ++ CurrentValueMapping}
                            end, {Acc, Vars, [Entry]}, SharedVarsL),
                % elp:ignore W0030
                maps:put(NewVars, NewValues, NewMap);
            none ->
                Acc#{Vars => [Entry]}
        end
    end, #{}, Constrs).

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
