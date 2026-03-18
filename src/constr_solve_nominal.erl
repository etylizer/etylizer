-module(constr_solve_nominal).

-include("log.hrl").

-export([
    has_nominal_constrs/2,
    check_nominal_constrs/2,
    check_nominal_combinations_only/2
]).

-type error() :: constr_solve:error().

% Result of a nominal pair check:
% - ok: types are nominally compatible (no conflict found, types could overlap)
% - skip: types cannot structurally overlap, so nominal checking is not applicable
% - {error, _}: nominal conflict found
-type nominal_result() :: ok | skip | {error, error()}.

%% ============================================================
%% Record definitions
%% ============================================================

% Variable subtyping graph: captures variable-to-variable edges from constraints,
% including edges nested inside matching compound types (tuples, lists, etc.).
% Compound types are positionally decomposed to extract all variable relationships.
-record(var_graph, {
    forward = #{} :: #{ast:ty_varname() => [ast:ty_varname()]},  % A <: B edges
    reverse = #{} :: #{ast:ty_varname() => [ast:ty_varname()]}   % B <: A edges (reverse of forward)
}).
-type var_graph() :: #var_graph{}.

% Precomputed derivation map: for each nominal type key, the set of nominal
% type keys it derives from (transitively). A nominal A derives from B if
% A's body contains B (directly or through non-nominal aliases).
% The relation is symmetric for compatibility checking.
-type derivation_map() :: #{symtab:ty_key() => sets:set(symtab:ty_key())}.

-record(var_info, {
    mater_map = #{} :: #{ast:ty_varname() => ast:ty()},     % scmater: T materializes into Alpha
    graph = #var_graph{} :: var_graph(),                     % variable-to-variable subtyping edges
    lower = #{} :: #{ast:ty_varname() => [ast:ty()]},        % concrete lower bounds (T <: var)
    upper = #{} :: #{ast:ty_varname() => [ast:ty()]},        % concrete upper bounds (var <: T)
    derivations = #{} :: derivation_map()                    % nominal derivation relationships
}).
-type var_info() :: #var_info{}.

%% ============================================================
%% Detection: does a constraint set involve nominal types?
%% ============================================================

% Check if any nominal types appear in the constraint set,
% including nominals hidden inside non-nominal type alias definitions.
% symtab:is_nominal could implement the recursive transitive check,
% but we implement it like this to keep symtab more simple.
-spec has_nominal_constrs(symtab:t(), constr:collected_constrs()) -> boolean().
has_nominal_constrs(Tab, Constrs) ->
    lists:any(
        fun ({scsubty, _, T1, T2}) ->
                ty_has_nominal(Tab, T1, sets:new()) orelse ty_has_nominal(Tab, T2, sets:new());
            ({scmater, _, T1, _}) -> ty_has_nominal(Tab, T1, sets:new());
            (_) -> false
        end,
        sets:to_list(Constrs)).

% Check if a type contains a nominal, either directly or transitively
% through non-nominal type alias definitions.
-spec ty_has_nominal(symtab:t(), ast:ty(), sets:set(ast:ty_ref())) -> boolean().
ty_has_nominal(Tab, Ty, Visited) ->
    utils:everything(
        fun ({named, _, Ref, _} = N) ->
                case symtab:is_nominal(Ref, Tab) of
                    true -> {ok, true};
                    false ->
                        case named_contains_nominal(Tab, N, Visited) of
                            true -> {ok, true};
                            false -> error
                        end
                end;
            (_) -> error
        end, Ty) =/= [].

% Check if a non-nominal named type transitively contains any nominal types.
% Unfolds one level and recursively checks non-nominal aliases found in the body.
-spec named_contains_nominal(symtab:t(), ast:ty(), sets:set(ast:ty_ref())) -> boolean().
named_contains_nominal(Tab, {named, Loc, Ref, Args}, Visited) ->
    case sets:is_element(Ref, Visited) of
        true -> false;
        false ->
            {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, Tab),
            VarNames = [V || {V, _Bound} <- Vars],
            case length(VarNames) =:= length(Args) of
                true ->
                    Map = subst:from_list(lists:zip(VarNames, Args)),
                    Expanded = subst:apply(Map, Body, no_clean),
                    ty_has_nominal(Tab, Expanded, sets:add_element(Ref, Visited));
                false -> false
            end
    end.

%% ============================================================
%% Per-combination nominal checking
%% ============================================================

% Check if any combination is nominally compatible (no structural check).
% Used after the flattened structural check has already passed.
-spec check_nominal_combinations_only(symtab:t(), constr_collect:all_combinations()) ->
    ok | {error, error()}.
check_nominal_combinations_only(_Tab, []) ->
    {error, {nominal_incompatible, ast:loc_auto(), "all branch combinations have nominal conflicts"}};
check_nominal_combinations_only(Tab, [{_SwitchedOff, SubtyConstrs} | Rest]) ->
    case check_nominal_constrs(Tab, SubtyConstrs) of
        ok -> ok;
        {error, _} -> check_nominal_combinations_only(Tab, Rest)
    end.

%% ============================================================
%% Nominal constraint checking
%% ============================================================

% Checks for nominal type incompatibilities in the collected constraints.
% Two nominal types with different names are never compatible.
% A nominal type is compatible with a non-nominal structural type (both directions).
%
% This check handles:
% - Variable chains: nominal types connected through scsubty variable chains
%   (e.g. meter() <: $1 <: $A <: foot() from polymorphic function calls)
% - Deep named types: nominal types hidden inside non-nominal type aliases
%   (e.g. wrapper(meter()) vs wrapper(foot()) where wrapper is not nominal)
% - Variables inside compound types: e.g. {tuple, [{var, $A}]} where $A
%   resolves to a nominal type through transitive chains
-spec check_nominal_constrs(symtab:t(), constr:collected_constrs()) -> ok | {error, error()}.
check_nominal_constrs(Tab, Constrs) ->
    ConstrList = sets:to_list(Constrs),
    VarInfo0 = build_var_info(Tab, ConstrList),
    VarInfo = VarInfo0#var_info{derivations = build_derivation_map(Tab)},
    lists:foldl(
        fun
            (_, {error, _} = Err) -> Err;
            ({scsubty, Loc, T1, T2}, ok) ->
                case check_nominal_pair(Tab, Loc, T1, T2, VarInfo, sets:new()) of
                    {error, _} = Err -> Err;
                    _ -> ok  % ok or skip both mean no conflict
                end;
            (_, ok) -> ok
        end,
        ok,
        ConstrList).

%% ============================================================
%% Variable bound analysis
%% ============================================================

-spec build_var_info(symtab:t(), [constr:simp_constr_subty() | constr:simp_constr_mater()]) -> var_info().
build_var_info(Tab, ConstrList) ->
    lists:foldl(fun(C, VI) ->
        case C of
            {scmater, _, T, Alpha} ->
                VI#var_info{mater_map = maps:put(Alpha, T, VI#var_info.mater_map)};
            {scsubty, _, T1, T2} ->
                add_type_pair(Tab, T1, T2, VI, sets:new());
            _ ->
                VI
        end
    end, #var_info{}, ConstrList).

% Process a type pair, extracting variable edges and concrete bounds.
% Recursively decomposes matching compound types to capture variable
% relationships at all nesting depths. Unfolds named types and mu types.
% The Visited set tracks type pairs to prevent infinite recursion.
-spec add_type_pair(symtab:t(), ast:ty(), ast:ty(), var_info(), sets:set()) -> var_info().
add_type_pair(_Tab, {var, A}, {var, B}, VI = #var_info{graph = G}, _Visited) ->
    % Use ty_variable ordering to determine edge direction:
    % the smaller variable (leq) is the lower bound.
    VA = ty_variable:new_with_name(A),
    VB = ty_variable:new_with_name(B),
    {Lo, Hi} = case ty_variable:leq(VA, VB) of
        true  -> {A, B};
        false -> {B, A}
    end,
    VI#var_info{graph = G#var_graph{
        forward = map_add(Lo, Hi, G#var_graph.forward),
        reverse = map_add(Hi, Lo, G#var_graph.reverse)}};
add_type_pair(_Tab, {var, V}, T, VI, _Visited) ->
    VI#var_info{upper = map_add(V, T, VI#var_info.upper)};
add_type_pair(_Tab, T, {var, V}, VI, _Visited) ->
    VI#var_info{lower = map_add(V, T, VI#var_info.lower)};
add_type_pair(Tab, {tuple, Elems1}, {tuple, Elems2}, VI, Visited)
        when length(Elems1) =:= length(Elems2) ->
    add_type_pairs(Tab, Elems1, Elems2, VI, Visited);
add_type_pair(Tab, {list, E1}, {list, E2}, VI, Visited) ->
    add_type_pair(Tab, E1, E2, VI, Visited);
add_type_pair(Tab, {nonempty_list, E1}, {nonempty_list, E2}, VI, Visited) ->
    add_type_pair(Tab, E1, E2, VI, Visited);
add_type_pair(Tab, {cons, H1, T1}, {cons, H2, T2}, VI, Visited) ->
    add_type_pairs(Tab, [H1, T1], [H2, T2], VI, Visited);
add_type_pair(Tab, {improper_list, H1, T1}, {improper_list, H2, T2}, VI, Visited) ->
    add_type_pairs(Tab, [H1, T1], [H2, T2], VI, Visited);
add_type_pair(Tab, {nonempty_improper_list, H1, T1}, {nonempty_improper_list, H2, T2}, VI, Visited) ->
    add_type_pairs(Tab, [H1, T1], [H2, T2], VI, Visited);
add_type_pair(Tab, {fun_full, Args1, Ret1}, {fun_full, Args2, Ret2}, VI, Visited)
        when length(Args1) =:= length(Args2) ->
    add_type_pairs(Tab, Args1 ++ [Ret1], Args2 ++ [Ret2], VI, Visited);
add_type_pair(Tab, {map, Assocs1}, {map, Assocs2}, VI, Visited)
        when length(Assocs1) =:= length(Assocs2) ->
    add_map_assoc_pairs(Tab, Assocs1, Assocs2, VI, Visited);
% Unions/intersections: pair each element against the other side.
% When both sides are unions/intersections, the one-sided clauses compose
% to produce all pairs transitively.
add_type_pair(Tab, {union, Elems}, T2, VI, Visited) ->
    lists:foldl(fun(E, Acc) -> add_type_pair(Tab, E, T2, Acc, Visited) end, VI, Elems);
add_type_pair(Tab, T1, {union, Elems}, VI, Visited) ->
    lists:foldl(fun(E, Acc) -> add_type_pair(Tab, T1, E, Acc, Visited) end, VI, Elems);
add_type_pair(Tab, {intersection, Elems}, T2, VI, Visited) ->
    lists:foldl(fun(E, Acc) -> add_type_pair(Tab, E, T2, Acc, Visited) end, VI, Elems);
add_type_pair(Tab, T1, {intersection, Elems}, VI, Visited) ->
    lists:foldl(fun(E, Acc) -> add_type_pair(Tab, T1, E, Acc, Visited) end, VI, Elems);
% Mu types: unwrap and recurse into body
add_type_pair(Tab, {mu, _, Body1}, T2, VI, Visited) ->
    add_type_pair(Tab, Body1, T2, VI, Visited);
add_type_pair(Tab, T1, {mu, _, Body2}, VI, Visited) ->
    add_type_pair(Tab, T1, Body2, VI, Visited);
% Negation types: recurse into body (nominal check is symmetric)
add_type_pair(Tab, {negation, T1}, {negation, T2}, VI, Visited) ->
    add_type_pair(Tab, T1, T2, VI, Visited);
add_type_pair(Tab, {negation, T1}, T2, VI, Visited) ->
    add_type_pair(Tab, T1, T2, VI, Visited);
add_type_pair(Tab, T1, {negation, T2}, VI, Visited) ->
    add_type_pair(Tab, T1, T2, VI, Visited);
% Both named types
add_type_pair(Tab, {named, L1, Ref1, Args1}, {named, L2, Ref2, Args2}, VI, Visited) ->
    case symtab:ref_to_key(Ref1) =:= symtab:ref_to_key(Ref2) andalso length(Args1) =:= length(Args2) of
        true ->
            % Same type constructor: decompose args pairwise
            add_type_pairs(Tab, Args1, Args2, VI, Visited);
        false ->
            % Different refs: unfold non-nominals and recurse
            unfold_and_add(Tab, {named, L1, Ref1, Args1}, {named, L2, Ref2, Args2}, VI, Visited)
    end;
% One side is a named type: unfold if non-nominal and recurse
add_type_pair(Tab, {named, L, Ref, Args}, T2, VI, Visited) ->
    unfold_left(Tab, {named, L, Ref, Args}, T2, VI, Visited);
add_type_pair(Tab, T1, {named, L, Ref, Args}, VI, Visited) ->
    unfold_right(Tab, T1, {named, L, Ref, Args}, VI, Visited);
add_type_pair(_Tab, _, _, VI, _Visited) -> VI.

-spec unfold_left(symtab:t(), ast:ty(), ast:ty(), var_info(), sets:set()) -> var_info().
unfold_left(Tab, {named, _, Ref, _} = N, T2, VI, Visited) ->
    Key = {N, T2},
    case sets:is_element(Key, Visited) orelse symtab:is_nominal(Ref, Tab) of
        true -> VI;
        false ->
            U = try_unfold(Tab, N),
            add_type_pair(Tab, U, T2, VI, sets:add_element(Key, Visited))
    end.

-spec unfold_right(symtab:t(), ast:ty(), ast:ty(), var_info(), sets:set()) -> var_info().
unfold_right(Tab, T1, {named, _, Ref, _} = N, VI, Visited) ->
    Key = {T1, N},
    case sets:is_element(Key, Visited) orelse symtab:is_nominal(Ref, Tab) of
        true -> VI;
        false ->
            U = try_unfold(Tab, N),
            add_type_pair(Tab, T1, U, VI, sets:add_element(Key, Visited))
    end.

-spec unfold_and_add(symtab:t(), ast:ty(), ast:ty(), var_info(), sets:set()) -> var_info().
unfold_and_add(Tab, {named, _, Ref1, _} = N1, {named, _, Ref2, _} = N2, VI, Visited) ->
    Key = {N1, N2},
    case sets:is_element(Key, Visited) of
        true -> VI;
        false ->
            Visited1 = sets:add_element(Key, Visited),
            case {symtab:is_nominal(Ref1, Tab), symtab:is_nominal(Ref2, Tab)} of
                {true, true} -> VI;
                {false, false} ->
                    add_type_pair(Tab, try_unfold(Tab, N1), try_unfold(Tab, N2), VI, Visited1);
                {true, false} ->
                    add_type_pair(Tab, N1, try_unfold(Tab, N2), VI, Visited1);
                {false, true} ->
                    add_type_pair(Tab, try_unfold(Tab, N1), N2, VI, Visited1)
            end
    end.

-spec add_type_pairs(symtab:t(), [ast:ty()], [ast:ty()], var_info(), sets:set()) -> var_info().
add_type_pairs(_Tab, [], [], VI, _Visited) -> VI;
add_type_pairs(Tab, [T1 | R1], [T2 | R2], VI, Visited) ->
    add_type_pairs(Tab, R1, R2, add_type_pair(Tab, T1, T2, VI, Visited), Visited).

-spec add_map_assoc_pairs(symtab:t(), [ast:ty_map_assoc()], [ast:ty_map_assoc()], var_info(), sets:set()) -> var_info().
add_map_assoc_pairs(_Tab, [], [], VI, _Visited) -> VI;
add_map_assoc_pairs(Tab, [{_, K1, V1} | R1], [{_, K2, V2} | R2], VI, Visited) ->
    VI1 = add_type_pair(Tab, K1, K2, add_type_pair(Tab, V1, V2, VI, Visited), Visited),
    add_map_assoc_pairs(Tab, R1, R2, VI1, Visited).

-spec map_add(K, V, #{K => [V]}) -> #{K => [V]}.
map_add(Key, Val, Map) ->
    maps:update_with(Key, fun(L) -> [Val | L] end, [Val], Map).

%% ============================================================
%% Nominal derivation map
%% ============================================================

% Build a map from each nominal type to the set of nominals it derives from
% (transitively). A nominal A derives from B if A's body contains B, either
% directly or through non-nominal aliases.
-spec build_derivation_map(symtab:t()) -> derivation_map().
build_derivation_map(Tab) ->
    Nominals = sets:to_list(symtab:get_nominals(Tab)),
    lists:foldl(fun(Key, Map) ->
        Derives = find_derived_nominals(Tab, Key, sets:new()),
        maps:put(Key, Derives, Map)
    end, #{}, Nominals).

% Find all nominal types that Key derives from (transitively).
-spec find_derived_nominals(symtab:t(), symtab:ty_key(), sets:set(symtab:ty_key())) -> sets:set(symtab:ty_key()).
find_derived_nominals(Tab, {ty_key, M, N, A} = Key, Visited) ->
    case sets:is_element(Key, Visited) of
        true -> sets:new();
        false ->
            Ref = {ty_ref, M, N, A},
            {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, ast:loc_auto(), Tab),
            VarNames = [V || {V, _Bound} <- Vars],
            % Use empty args for arity-0 types, placeholder anys for parameterized
            Args = [{predef, any} || _ <- VarNames],
            SubstBody = case length(VarNames) =:= length(Args) andalso Args =/= [] of
                true ->
                    Map = subst:from_list(lists:zip(VarNames, Args)),
                    subst:apply(Map, Body, no_clean);
                false -> Body
            end,
            % Find all nominal refs in the body
            Visited1 = sets:add_element(Key, Visited),
            DirectNominals = collect_nominal_refs(Tab, SubstBody),
            % Transitively find derivations of each direct nominal
            sets:fold(fun(DerivedKey, Acc) ->
                Transitive = find_derived_nominals(Tab, DerivedKey, Visited1),
                sets:union(sets:add_element(DerivedKey, Transitive), Acc)
            end, DirectNominals, DirectNominals)
    end.

% Collect all nominal type keys referenced in a type expression.
-spec collect_nominal_refs(symtab:t(), ast:ty()) -> sets:set(symtab:ty_key()).
collect_nominal_refs(Tab, Ty) ->
    Refs = utils:everything(
        fun ({named, _, Ref, _}) ->
                case symtab:is_nominal(Ref, Tab) of
                    true -> {ok, symtab:ref_to_key(Ref)};
                    false -> error
                end;
            (_) -> error
        end, Ty),
    sets:from_list(Refs).

% Check if two nominal types are compatible: same type or one derives from the other.
-spec are_nominals_compatible(symtab:ty_key(), symtab:ty_key(), derivation_map()) -> boolean().
are_nominals_compatible(Key, Key, _) -> true;
are_nominals_compatible(Key1, Key2, DerivMap) ->
    derives_from(Key1, Key2, DerivMap) orelse derives_from(Key2, Key1, DerivMap).

-spec derives_from(symtab:ty_key(), symtab:ty_key(), derivation_map()) -> boolean().
derives_from(Key1, Key2, DerivMap) ->
    case maps:find(Key1, DerivMap) of
        {ok, Derives} -> sets:is_element(Key2, Derives);
        error -> false
    end.

% Compute transitive lower bounds of a variable: all concrete types T
% such that T <: ... <: V through scsubty variable chains, scmater, and
% direct scsubty(_, ConcreteT, {var,V}) constraints.
-spec trans_lower(ast:ty_varname(), var_info(), sets:set(ast:ty_varname())) -> [ast:ty()].
trans_lower(V, VarInfo = #var_info{mater_map = MM, graph = G, lower = CL}, Visited) ->
    case sets:is_element(V, Visited) of
        true -> [];
        false ->
            Visited1 = sets:add_element(V, Visited),
            Direct = maps:get(V, CL, []) ++
                case maps:find(V, MM) of
                    {ok, T} -> [T];
                    error -> []
                end,
            % Follow reverse edges: for each P where P <: V, include P's lower bounds
            Preds = maps:get(V, G#var_graph.reverse, []),
            Indirect = lists:flatmap(fun(P) ->
                trans_lower(P, VarInfo, Visited1)
            end, Preds),
            Direct ++ Indirect
    end.

% Compute transitive upper bounds of a variable: all concrete types T
% such that V <: ... <: T through scsubty variable chains and
% direct scsubty(_, {var,V}, ConcreteT) constraints.
-spec trans_upper(ast:ty_varname(), var_info(), sets:set(ast:ty_varname())) -> [ast:ty()].
trans_upper(V, VarInfo = #var_info{graph = G, upper = CU}, Visited) ->
    case sets:is_element(V, Visited) of
        true -> [];
        false ->
            Visited1 = sets:add_element(V, Visited),
            Direct = maps:get(V, CU, []),
            % Follow forward edges: for each S where V <: S, include S's upper bounds
            Succs = maps:get(V, G#var_graph.forward, []),
            Indirect = lists:flatmap(fun(S) ->
                trans_upper(S, VarInfo, Visited1)
            end, Succs),
            Direct ++ Indirect
    end.

%% ============================================================
%% Pairwise nominal compatibility checking
%% ============================================================

% Check a pair of types for nominal incompatibility.
% Returns ok (compatible), skip (types can't overlap, not applicable),
% or {error, _} (nominal conflict found).
% When a type variable is encountered, ALL its transitive bounds are checked:
% lower bounds for LHS variables, upper bounds for RHS variables.
% Recurses into compound types and unfolds non-nominal named types.
% The Seen set tracks (T1, T2) pairs to detect cycles in recursive types.
-spec check_nominal_pair(symtab:t(), ast:loc(), ast:ty(), ast:ty(), var_info(), sets:set()) ->
    nominal_result().
check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen) ->
    Key = {T1, T2},
    case sets:is_element(Key, Seen) of
        true -> ok; % cycle in recursive types: can't prove incompatibility
        false ->
            check_nominal_pair_inner(Tab, Loc, T1, T2, VarInfo, sets:add_element(Key, Seen))
    end.

-spec check_nominal_pair_inner(symtab:t(), ast:loc(), ast:ty(), ast:ty(), var_info(), sets:set()) ->
    nominal_result().
% LHS is a variable: resolve to all transitive lower bounds and check each
check_nominal_pair_inner(Tab, Loc, {var, Alpha}, T2, VarInfo, Seen) ->
    Lowers = trans_lower(Alpha, VarInfo, sets:new()),
    check_any_against(Tab, Loc, Lowers, T2, VarInfo, Seen);
% RHS is a variable: resolve to all transitive upper bounds and check each
check_nominal_pair_inner(Tab, Loc, T1, {var, Beta}, VarInfo, Seen) ->
    Uppers = trans_upper(Beta, VarInfo, sets:new()),
    check_against_any(Tab, Loc, T1, Uppers, VarInfo, Seen);
% LHS is a union: each element must be compatible with RHS
check_nominal_pair_inner(Tab, Loc, {union, Elems}, T2, VarInfo, Seen) ->
    check_any_against(Tab, Loc, Elems, T2, VarInfo, Seen);
% RHS is a union: LHS must be compatible with at least one element
check_nominal_pair_inner(Tab, Loc, T1, {union, Elems}, VarInfo, Seen) ->
    check_against_some(Tab, Loc, T1, Elems, VarInfo, Seen);
% LHS is an intersection: every element must be compatible with RHS,
% because a value in the intersection carries all nominal identities simultaneously
check_nominal_pair_inner(Tab, Loc, {intersection, Elems}, T2, VarInfo, Seen) ->
    check_any_against(Tab, Loc, Elems, T2, VarInfo, Seen);
% RHS is an intersection: LHS must be compatible with every element
check_nominal_pair_inner(Tab, Loc, T1, {intersection, Elems}, VarInfo, Seen) ->
    check_against_any(Tab, Loc, T1, Elems, VarInfo, Seen);
% Mu types: unwrap and check the body (Seen set handles cycles)
check_nominal_pair_inner(Tab, Loc, {mu, _, Body1}, T2, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, Body1, T2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, T1, {mu, _, Body2}, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, T1, Body2, VarInfo, Seen);
% Negation types: recurse into body (nominal check is symmetric)
check_nominal_pair_inner(Tab, Loc, {negation, T1}, {negation, T2}, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, {negation, T1}, T2, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, T1, {negation, T2}, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen);
% Both named types
check_nominal_pair_inner(Tab, Loc, {named, _, Ref1, Args1}, {named, _, Ref2, Args2}, VarInfo, Seen) ->
    case symtab:ref_to_key(Ref1) =:= symtab:ref_to_key(Ref2) of
        true when length(Args1) =:= length(Args2) ->
            % Same type constructor (nominal or not): check args pairwise
            check_nominal_pairs(Tab, Loc, Args1, Args2, VarInfo, Seen);
        true ->
            ok;
        false ->
            case {symtab:is_nominal(Ref1, Tab), symtab:is_nominal(Ref2, Tab)} of
                {true, true} ->
                    % Two different nominal types: check derivation via precomputed map
                    Key1 = symtab:ref_to_key(Ref1),
                    Key2 = symtab:ref_to_key(Ref2),
                    case are_nominals_compatible(Key1, Key2, VarInfo#var_info.derivations) of
                        true -> ok;
                        false ->
                            nominal_error(Loc, {named, Loc, Ref1, Args1}, {named, Loc, Ref2, Args2})
                    end;
                {false, false} ->
                    % Both non-nominal, different refs: unfold both and check
                    U1 = try_unfold(Tab, {named, Loc, Ref1, Args1}),
                    U2 = try_unfold(Tab, {named, Loc, Ref2, Args2}),
                    check_nominal_pair(Tab, Loc, U1, U2, VarInfo, Seen);
                {true, false} ->
                    U2 = try_unfold(Tab, {named, Loc, Ref2, Args2}),
                    check_nominal_pair(Tab, Loc, {named, Loc, Ref1, Args1}, U2, VarInfo, Seen);
                {false, true} ->
                    U1 = try_unfold(Tab, {named, Loc, Ref1, Args1}),
                    check_nominal_pair(Tab, Loc, U1, {named, Loc, Ref2, Args2}, VarInfo, Seen)
            end
    end;
% Compound types with matching shapes: recurse into components
check_nominal_pair_inner(Tab, Loc, {tuple, Elems1}, {tuple, Elems2}, VarInfo, Seen)
        when length(Elems1) =:= length(Elems2) ->
    check_nominal_pairs(Tab, Loc, Elems1, Elems2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, {list, E1}, {list, E2}, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, E1, E2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, {nonempty_list, E1}, {nonempty_list, E2}, VarInfo, Seen) ->
    check_nominal_pair(Tab, Loc, E1, E2, VarInfo, Seen);
check_nominal_pair_inner(Tab, Loc, {cons, H1, T1}, {cons, H2, T2}, VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, H1, H2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen))
    end;
check_nominal_pair_inner(Tab, Loc, {improper_list, H1, T1}, {improper_list, H2, T2}, VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, H1, H2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen))
    end;
check_nominal_pair_inner(Tab, Loc, {nonempty_improper_list, H1, T1}, {nonempty_improper_list, H2, T2}, VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, H1, H2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen))
    end;
check_nominal_pair_inner(Tab, Loc, {fun_full, Args1, Ret1}, {fun_full, Args2, Ret2}, VarInfo, Seen)
        when length(Args1) =:= length(Args2) ->
    case check_nominal_pairs(Tab, Loc, Args1, Args2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_nominal_pair(Tab, Loc, Ret1, Ret2, VarInfo, Seen))
    end;
% Map types: check association keys and values pairwise
check_nominal_pair_inner(Tab, Loc, {map, Assocs1}, {map, Assocs2}, VarInfo, Seen)
        when length(Assocs1) =:= length(Assocs2) ->
    {Ks1, Vs1} = lists:unzip([{K, V} || {_, K, V} <- Assocs1]),
    {Ks2, Vs2} = lists:unzip([{K, V} || {_, K, V} <- Assocs2]),
    check_nominal_pairs(Tab, Loc, Ks1 ++ Vs1, Ks2 ++ Vs2, VarInfo, Seen);
% One side is a non-nominal named type, other is structural: unfold and re-check
check_nominal_pair_inner(Tab, Loc, {named, _, Ref, _Args} = N, T2, VarInfo, Seen) ->
    case symtab:is_nominal(Ref, Tab) of
        true -> ok; % nominal vs non-named structural: no conflict
        false ->
            U = try_unfold(Tab, N),
            check_nominal_pair(Tab, Loc, U, T2, VarInfo, Seen)
    end;
check_nominal_pair_inner(Tab, Loc, T1, {named, _, Ref, _Args} = N, VarInfo, Seen) ->
    case symtab:is_nominal(Ref, Tab) of
        true -> ok; % non-named structural vs nominal: no conflict
        false ->
            U = try_unfold(Tab, N),
            check_nominal_pair(Tab, Loc, T1, U, VarInfo, Seen)
    end;
% Types with no nominal content or incompatible shapes: nothing to check
check_nominal_pair_inner(_Tab, _Loc, _T1, _T2, _VarInfo, _Seen) -> skip.

% Combine two nominal results: error always propagates, ok + ok = ok,
% skip + ok = ok, skip + skip = skip.
% The first argument is always ok | skip (callers short-circuit errors).
-spec combine_results(ok | skip, nominal_result()) -> nominal_result().
combine_results(_, {error, _} = Err) -> Err;
combine_results(ok, _) -> ok;
combine_results(skip, R) -> R.

%% ============================================================
%% List checking helpers
%% ============================================================

% Check each type in the list against T2. All must be compatible.
% Returns ok if all return ok, skip if any returns skip (and none error),
% error on first error.
-spec check_any_against(symtab:t(), ast:loc(), [ast:ty()], ast:ty(), var_info(), sets:set()) ->
    nominal_result().
check_any_against(_Tab, _Loc, [], _T2, _VarInfo, _Seen) -> ok;
check_any_against(Tab, Loc, [T1 | Rest], T2, VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_any_against(Tab, Loc, Rest, T2, VarInfo, Seen))
    end.

% Check T1 against each type in the list. All must be compatible.
-spec check_against_any(symtab:t(), ast:loc(), ast:ty(), [ast:ty()], var_info(), sets:set()) ->
    nominal_result().
check_against_any(_Tab, _Loc, _T1, [], _VarInfo, _Seen) -> ok;
check_against_any(Tab, Loc, T1, [T2 | Rest], VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_against_any(Tab, Loc, T1, Rest, VarInfo, Seen))
    end.

% Check T1 against a union: find a compatible element.
% - ok: found a structurally plausible element with no nominal conflict -> accept
% - skip: types can't overlap with this element -> try next
% - error: nominal conflict with this element -> try next, but remember the error
% If all plausible elements have conflicts, return the last error.
% If no plausible elements exist (all skip), return ok (no nominal concern).
-spec check_against_some(symtab:t(), ast:loc(), ast:ty(), [ast:ty()], var_info(), sets:set()) ->
    nominal_result().
check_against_some(Tab, Loc, T1, Elems, VarInfo, Seen) ->
    check_against_some(Tab, Loc, T1, Elems, VarInfo, Seen, no_match).

-spec check_against_some(symtab:t(), ast:loc(), ast:ty(), [ast:ty()], var_info(), sets:set(),
    no_match | {error, error()}) -> nominal_result().
check_against_some(_Tab, _Loc, _T1, [], _VarInfo, _Seen, no_match) -> ok;
check_against_some(_Tab, _Loc, _T1, [], _VarInfo, _Seen, {error, _} = Err) -> Err;
check_against_some(Tab, Loc, T1, [T2 | Rest], VarInfo, Seen, LastErr) ->
    case check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen) of
        ok -> ok;
        skip -> check_against_some(Tab, Loc, T1, Rest, VarInfo, Seen, LastErr);
        {error, _} = Err -> check_against_some(Tab, Loc, T1, Rest, VarInfo, Seen, Err)
    end.

-spec check_nominal_pairs(symtab:t(), ast:loc(), [ast:ty()], [ast:ty()], var_info(), sets:set()) ->
    nominal_result().
check_nominal_pairs(_Tab, _Loc, [], [], _VarInfo, _Seen) -> ok;
check_nominal_pairs(Tab, Loc, [T1 | Rest1], [T2 | Rest2], VarInfo, Seen) ->
    case check_nominal_pair(Tab, Loc, T1, T2, VarInfo, Seen) of
        {error, _} = Err -> Err;
        R1 -> combine_results(R1, check_nominal_pairs(Tab, Loc, Rest1, Rest2, VarInfo, Seen))
    end.


%% ============================================================
%% Type unfolding helpers
%% ============================================================

% Unfold a non-nominal named type one step by substituting args into the body.
-spec try_unfold(symtab:t(), ast:ty()) -> ast:ty().
try_unfold(Tab, {named, Loc, Ref, Args}) ->
    {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, Tab),
    VarNames = [V || {V, _Bound} <- Vars],
    case length(VarNames) =:= length(Args) of
        true ->
            Map = subst:from_list(lists:zip(VarNames, Args)),
            subst:apply(Map, Body, no_clean);
        false -> {named, Loc, Ref, Args}
    end.


-spec nominal_error(ast:loc(), ast:ty(), ast:ty()) -> {error, error()}.
nominal_error(Loc, T1, T2) ->
    Hint = utils:sformat("~s is not compatible with ~s",
        pretty:render_ty(T1), pretty:render_ty(T2)),
    {error, {nominal_incompatible, Loc, Hint}}.
