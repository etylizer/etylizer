-module(constr_solve).

-include("log.hrl").

-export([
    check_simp_constrs/4,
    check_simp_constrs_return_unmatched/4,
    solve_simp_constrs/3
]).

-export_type([
    error/0,
    error_kind/0
]).

-ifdef(TEST).
-export([search_failing_prefix/3]).
-endif.

-type error_kind() :: constr_error_locs:constr_error_kind().
-type error() :: {error_kind(), ast:loc(), string()}.

% Ignores unmatched branches, just returns their locations.
-spec check_simp_constrs_return_unmatched(
    symtab:t(),
    sets:set(ast:ty_varname()),
    constr:simp_constrs(),
    string()) ->
    {ok, Unmachted::sets:set(ast:loc())} | {error, error() | none}.
check_simp_constrs_return_unmatched(Tab, FixedTyvars, Ds, What) ->
    % ?LOG_DEBUG("Constraints:~n~s", pretty:render_constr(Ds)),
    SubtyConstrsDisj = constr_collect:collect_constrs_all_combinations(Ds),
    N = length(SubtyConstrsDisj),
    ?LOG_DEBUG("Found ~w conjunctions of constraints while type checking ~s", N, What),
    % SubtyConstrsDisj contains, for each conjunction, a set of
    % locations of branches that are switched off (do not match). If a conjunction
    % is satisifiable, we must return the set of locations. If a location is contained
    % in all sets for all intersection types, the branch at this location never matches,
    % so it's an error.
    case lists:foldl(
        fun ({I, {SwitchedOffBranches, SubtyConstrs}}, Acc) ->
            case Acc of
                false ->
                    ?LOG_DEBUG("Checking conjunction ~w/~w for satisfiability:~n~s",
                        I, N, pretty:render_constr(SubtyConstrs)),
                    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
                        false -> false;
                        true -> {true, SwitchedOffBranches}
                    end;
                {true, X} -> {true, X}
            end
        end,
        false,
        utils:with_index(1, SubtyConstrsDisj))
    of
        {true, SwitchedOffBranches} -> {ok, SwitchedOffBranches};
        false -> {error, none} % FIXME: error locations
    end.

% Check if dynamic() appears anywhere in the constraint set.
% If so, redundancy checks are skipped entirely because dynamic() is consistent
% with both T and not(T) for any T, making the satisfiability-based redundancy
% check unsound.
%
% Implementation: precompute (once per process / symtab) the set of named-type
% refs whose body transitively contains `{predef, dynamic}`. Then for each
% constraint type, walk it WITHOUT unfolding and check for `{predef, dynamic}`
% directly OR any `{named, _, Ref, _}` whose Ref is in the precomputed set.
%
% This avoids the previous per-constraint `ast_utils:unfold_ty` call which
% built a fully-expanded copy of every constraint type (≈8 s on a 16-constraint
% set involving ast:exp()) just to scan for one literal.
-spec has_dynamic_constr(symtab:t(), constr:collected_constrs()) -> boolean().
has_dynamic_constr(Tab, Constrs) ->
    DynRefs = get_dyn_refs(Tab),
    TyHasDynamic = fun(Ty) ->
        utils:everything(
          fun({predef, dynamic}) -> {ok, true};
             ({named, _, Ref, _}) ->
                 case sets:is_element(normalize_ref(Ref), DynRefs) of
                     true -> {ok, true};
                     false -> error
                 end;
             (_) -> error
          end, Ty) =/= []
    end,
    lists:any(
        fun ({scsubty, _, T1, T2}) -> TyHasDynamic(T1) orelse TyHasDynamic(T2);
            ({scmater, _, T1, _}) -> TyHasDynamic(T1);
            (_) -> false
        end,
        sets:to_list(Constrs)).

%% AST uses `{ty_ref, M, N, A}` and `{ty_qref, M, N, A}` for named-type
%% references; the symtab keys them as `{ty_key, M, N, A}`. Normalize so
%% the precomputed dyn set and the constraint walk speak the same language.
normalize_ref({ty_ref, M, N, A})  -> {ty_key, M, N, A};
normalize_ref({ty_qref, M, N, A}) -> {ty_key, M, N, A};
normalize_ref(Other)              -> Other.

%% Process-dict-cached set of named-type refs that transitively reference
%% `{predef, dynamic}`. Recomputed once per symtab (keyed by erlang:phash2/1
%% of the type-map to detect changes across function checks).
get_dyn_refs(Tab) ->
    Types = symtab:get_types(Tab),
    Key = erlang:phash2(Types),
    case erlang:get({'$dyn_refs', Key}) of
        undefined ->
            Set = compute_dyn_refs(Types),
            erlang:put({'$dyn_refs', Key}, Set),
            Set;
        Set ->
            Set
    end.

compute_dyn_refs(Types) ->
    %% Direct: which refs have {predef, dynamic} directly in their body
    %% Edges: ref -> set of refs it directly references in its body
    %% (refs normalized to the symtab's ty_key form so the closure unifies
    %% ty_ref / ty_qref / ty_key from the various AST sites)
    {Direct, Edges} = maps:fold(
      fun(Ref, {ty_scheme, _, Body}, {DAcc, EAcc}) ->
            BodyHasDyn = utils:everything(
                fun({predef, dynamic}) -> {ok, true}; (_) -> error end, Body) =/= [],
            BodyRefs = sets:from_list(
                [normalize_ref(R) || R <- utils:everything(
                    fun({named, _, R, _}) -> {ok, R}; (_) -> error end, Body)]),
            DAcc1 = case BodyHasDyn of
                        true  -> sets:add_element(Ref, DAcc);
                        false -> DAcc
                    end,
            {DAcc1, EAcc#{Ref => BodyRefs}}
      end, {sets:new(), #{}}, Types),
    %% Fixpoint: add a ref if any of its referenced refs is already in.
    closure_dyn_refs(Direct, Edges).

closure_dyn_refs(Set, Edges) ->
    NewSet = maps:fold(
      fun(Ref, RefsOut, Acc) ->
            case sets:is_element(Ref, Acc) of
                true  -> Acc;
                false ->
                    case sets:fold(
                           fun(R, A) -> A orelse sets:is_element(R, Acc) end,
                           false, RefsOut)
                    of
                        true  -> sets:add_element(Ref, Acc);
                        false -> Acc
                    end
            end
      end, Set, Edges),
    case sets:size(NewSet) =:= sets:size(Set) of
        true  -> Set;
        false -> closure_dyn_refs(NewSet, Edges)
    end.

-spec check_redundant_branch(symtab:t(), sets:set(ast:ty_varname()), constr:subty_constrs(),
    {ast:loc(), constr:subty_constrs()}, ok | {error, error()}) -> ok | {error, error()}.
check_redundant_branch(_Tab, _FixedTyvars, _SubtyConstrs, _LocAndConstrs, Acc = {error, _}) -> Acc;
check_redundant_branch(Tab, FixedTyvars, SubtyConstrs, {Loc, UnmatchedConstrs}, ok) ->
    All = sets:union(UnmatchedConstrs, SubtyConstrs),
    case is_satisfiable(Tab, All, FixedTyvars, "redundancy check") of
        true ->
            ?LOG_DEBUG("Branch at ~s is redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                ast:format_loc(Loc),
                pretty:render_constr(UnmatchedConstrs),
                sets:to_list(FixedTyvars)),
            {error, {redundant_branch, Loc, ""}};
        false ->
            ?LOG_DEBUG("Branch at ~s is not redundant. Constraints that were added to the constraint above: ~s~nFixed: ~200p",
                ast:format_loc(Loc),
                pretty:render_constr(UnmatchedConstrs),
                sets:to_list(FixedTyvars)),
            ok
    end.

-spec locate_unsat_error(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs()) ->
    {error, error() | none}.
locate_unsat_error(Tab, FixedTyvars, Ds) ->
    Blocks = constr_error_locs:simp_constrs_to_blocks(Ds),
    ?LOG_DEBUG("Constraints are not satisfiable, now locating source of errors. Blocks:~n~s",
        pretty:render_list(fun pretty:constr_block/1, Blocks)),
    Timeout = 4000,
    TimeoutRes = utils:timeout(Timeout, fun () -> locate_tyerror(Tab, FixedTyvars, Blocks) end),
    case TimeoutRes of
        {ok, Res} -> Res;
        timeout ->
            ?LOG_INFO("Locating type error timed out after ~wms", Timeout),
            {error, none}
    end.

% Treats unmatched branches as errors.
-spec check_simp_constrs(symtab:t(), sets:set(ast:ty_varname()), constr:simp_constrs(), string()) ->
    ok | {error, error() | none}.
check_simp_constrs(Tab, FixedTyvars, Ds, What) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    ?LOG_DEBUG("Checking constraints for satisfiability to type check ~s:~n~s~nFixed: ~s",
        What, pretty:render_constr(SubtyConstrs), pretty:render_set(fun pretty:atom/1, FixedTyvars)),
    case is_satisfiable(Tab, SubtyConstrs, FixedTyvars, "satisfiability check") of
        true ->
            % check for redundant branches
            ReduDs = constr_collect:collect_matching_cond_constrs(Ds),
            ?LOG_DEBUG("Constraints are satisfiable, now checking ~w branches for redundancy",
                length(ReduDs)),
            case has_dynamic_constr(Tab, SubtyConstrs) of
                true ->
                    ?LOG_DEBUG("Skipping all redundancy checks (dynamic() found in constraints)"),
                    ok;
                false ->
                    lists:foldl(
                        fun (LocAndConstrs, Acc) ->
                            check_redundant_branch(Tab, FixedTyvars, SubtyConstrs, LocAndConstrs, Acc)
                        end,
                        ok,
                        ReduDs)
            end;
        false ->
            locate_unsat_error(Tab, FixedTyvars, Ds)
    end.

% search_failing_prefix(L, F, Pred, Acc).
% Returns the list element Xi of L with the smallest index i such that
% Pred(F(X1) union ... union F(Xi)) yields false.
% That is, for all j < i: Pred(Acc union F(X1) union ... union F(Xj)) yields true.
% Precondition: Pred(F(X1) union ... union F(Xn)), where n is the length of L, must be false.
-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean())) -> T.
search_failing_prefix(L, F, Pred) ->
    N = length(L),
    ?LOG_DEBUG("Search for a minimal unsatisfiable prefix in ~w blocks", N),
    I = search_failing_prefix(L, F, Pred, 1, N),
    lists:nth(I, L).

% Helper function for search_failing_prefix.
% We some sort of binary search here to minimize the calls of Pred. (In reality, Pred is tally,
% which is expensive.)
% Left and Right are the (inclusive) boundaries of the search, starting at 1.
% Invariants: Left <= Right and Pred(F(X1) union ... union F(X_Right)) yields false
-spec search_failing_prefix(
    list(T), fun((T) -> sets:set(U)), fun((sets:set(U)) -> boolean()), integer(), integer())
    -> integer().
search_failing_prefix(L, F, Pred, Left, Right) ->
    Mid = (Left + Right) div 2,
    Prefix = lists:sublist(L, Mid), % take all elements until Mid (inclusive)
    ?LOG_DEBUG("Checking if the first ~w blocks are satisifiable", Mid),
    Set = sets:union(lists:map(F, Prefix)),
    Res = Pred(Set),
    % io:format("  Left=~w, Right=~w, Mid=~w, Res=~w, Prefix=~w~n", [Left, Right, Mid, Res, Prefix]),
    case Res of
        false ->
            case Left >= Right of
                true -> Mid;
                false -> search_failing_prefix(L, F, Pred, Left, Mid)
            end;
        true ->
            case Left >= Right of
                true -> Right;
                false -> search_failing_prefix(L, F, Pred, Mid + 1, Right)
            end
    end.

-spec locate_tyerror(symtab:t(), sets:set(ast:ty_varname()), constr_error_locs:constr_blocks())
    -> {error, error() | none}.
locate_tyerror(Tab, FreeSet, Blocks) ->
    Extract = fun({_Kind, _Span, _What, Ds}) -> Ds end,
    Pred = fun(Ds) -> is_satisfiable(Tab, Ds, FreeSet, "error location") end,
    {Kind, Span, _What, _Ds} = search_failing_prefix(Blocks, Extract, Pred),
    {error, {Kind, Span, ""}}.

-spec format_tally_error([{error, string()}]) -> string().
format_tally_error([]) -> "(no specific error messages)";
format_tally_error(ErrList) ->
    {ErrListShort, N} = utils:shorten(ErrList, 20),
    "\n" ++ string:join(
      lists:map(
        fun({error, Msg}) -> "    " ++ Msg end, ErrListShort),
      "\n") ++
    (if N =:= 0 -> "";
        true -> utils:sformat("~n    (skipped ~w lines)", N)
     end).

-spec is_satisfiable(symtab:t(), constr:collected_constrs(), sets:set(ast:ty_varname()), string()) -> boolean().
is_satisfiable(Tab, Constrs, Fixed, What) ->
    {SatisfyRes, Delta} = utils:timing(fun() -> tally:is_satisfiable(Tab, Constrs, Fixed) end),
    case SatisfyRes of
        {false, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            false;
        {true, _} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            true
    end.

-spec solve_simp_constrs(symtab:t(), constr:simp_constrs(), string()) -> error | nonempty_list(subst:t()).
solve_simp_constrs(Tab, Ds, What) ->
    SubtyConstrs = constr_collect:collect_constrs_no_matching_cond(Ds),
    {Res, Delta} = utils:timing(fun() -> tally:tally(Tab, SubtyConstrs) end),
    case Res of
        {error, ErrList} ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally finished with errors.", What, Delta),
            ?LOG_TRACE("Tally errors: ~s", format_tally_error(ErrList)),
            error;
        Substs ->
            ?LOG_DEBUG("Tally time (~s): ~pms, tally successful.", What, Delta),
            ?LOG_TRACE("Substitutions:~n~s", [pretty:render_substs(Substs)]),
            Substs
    end.
