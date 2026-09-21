-module(subst).

-compile({no_auto_import,[apply/3]}).

-include("log.hrl").

-export_type([
    t/0,
    base_subst/0,
    tally_subst/0
]).

-export([
    apply/3,
    apply_base/2,
    from_list/1,
    empty/0,
    extend/3,
    mk_tally_subst/2,
    base_subst/1,
    collect_vars/5,
    clean_cons/3
]).

-ifdef(TEST).
-export([
    clean/3
]).
-endif.


-type base_subst() :: #{ ast:ty_varname() => ast:ty() }.

-type tally_subst() :: {tally_subst, base_subst(), sets:set(ast:ty_varname())}.

-type t() :: base_subst() | tally_subst().

-spec base_subst(t()) -> base_subst().
base_subst({tally_subst, S, _}) -> S;
base_subst(S) -> S.

-spec clean(ast:ty(), sets:set(ast:ty_varname()), term()) -> ast:ty().
clean(T, Fixed, SymTab) ->
    % clean
    Cleaned = clean_type(T, Fixed, SymTab),
    % simplify by converting into internal type and back (processes any() and none() replacements)
    Parsed = ty_parser:parse(Cleaned),
    Res = ty_parser:unparse(Parsed),
    % FIXME remove sanity at some point
    true = ty_node:leq(Parsed, ty_parser:parse(T)),
    Res.

-spec clean_cons([{ast:ty(), ast:ty()}], sets:set(ast:ty_varname()), symtab:t()) -> [{ast:ty(), ast:ty()}].
clean_cons(CList, Fixed, SymTab) ->
    %% Phase 1: monovariant variance-based clean (existing).
    %% Per-schema variance is precomputed via fixpoint over symtab:get_types/1 and
    %% threaded as a read-only argument; this lets collect_vars treat
    %% {named, _, Ref, Args} as a leaf, walking only Args with the correct
    %% polarity per parameter
    VCache = compute_variance_cache(SymTab),
    VarPositions = collect_vars_clist(CList, 0, #{}, Fixed, VCache),

    Apply = fun(Ty) -> maps:fold(
        fun(VariableName, VariablePositions, Tyy) ->
            case lists:usort(VariablePositions) of
                [0] -> apply_base(#{VariableName => {predef, none}}, Tyy);
                [1] -> apply_base(#{VariableName => {predef, any}}, Tyy);
                _ -> Tyy
            end
        end, Ty, VarPositions)
            end,

    %% Phase 1.5: structural simplification of intersections/unions.
    %% intersection drops top arms; union drops bottom arms. Reduces the
    %% BDD work the solver has to do for each constraint — these patterns
    %% show up often after constraint generation produces e.g.
    %% `intersection([specific_2tuple, tuple(any,any)])` where the second
    %% arg is universal and contributes nothing.
    CList1 = lists:flatmap(
        fun({C1, C2}) ->
            S = simplify_ty(Apply(C1)),
            T = simplify_ty(Apply(C2)),
            %% Sound constraint splitting:
            %%   union(S1..Sm) <: T          ⟺  S1 <: T ∧ … ∧ Sm <: T
            %%   S <: intersection(T1..Tn)   ⟺  S <: T1 ∧ … ∧ S <: Tn
            %% Both replace one "compound boundary" constraint with multiple
            %% smaller ones. Tally's per-constraint BDD work shrinks, partition
            %% structure changes (variables may end up in fewer constraints).
            LHSs = case S of
                {union, Args1} when length(Args1) > 1 -> Args1;
                _ -> [S]
            end,
            RHSs = case T of
                {intersection, Args2} when length(Args2) > 1 -> Args2;
                _ -> [T]
            end,
            [{L, R} || L <- LHSs, R <- RHSs]
        end, CList),
    %% Phase 2: top-level peeling fixpoint. A variable V whose every occurrence
    %% in CList is the *direct* top of a constraint side (i.e., the side equals
    %% {var, V}) is eliminated by substituting V := union of its lower bounds
    %% (or none() if no lower bound). Sound for satisfiability without an
    %% L<:U check: every model of the original restricts to V := L for the
    %% substituted system, and vice versa.
    %%
    %% Surgical (A3): relaxed rule. V is peelable iff for every constraint:
    %%   - V is the direct top of one side, OR
    %%   - V appears nested with consistent polarity:
    %%       all nested occurrences at polarity 0 → V := union(lowers)
    %%       all nested occurrences at polarity 1 → V := intersect(uppers)
    %% Always-on. Runs to fixed point — termination is guaranteed because each
    %% iteration eliminates one polyvar.
    peel_loop(CList1, Fixed, length(CList1) + 1024).

%% Iterative top-level peeling. The fuel guard (Rounds) prevents pathological
%% loops; in practice we converge in O(#peeled) rounds.
-spec peel_loop([{ast:ty(), ast:ty()}], sets:set(ast:ty_varname()), non_neg_integer()) ->
    [{ast:ty(), ast:ty()}].
peel_loop(CList, _Fixed, 0) -> CList;
peel_loop(CList, Fixed, Rounds) ->
    case find_peelables(CList, Fixed) of
        [] -> drop_tautologies(resplit_unions(CList));
        Peelables ->
            PVars = sets:from_list([V || {V, _} <- Peelables], [{version, 2}]),
            Independent = [{V, T} || {V, T} <- Peelables, not type_has_any_var(T, sets:del_element(V, PVars))],
            Batch = case Independent of
                        [] -> [hd(Peelables)];
                        _ -> Independent
                    end,
            Subst = maps:from_list(Batch),
            CList1 = [{apply_base(Subst, C1), apply_base(Subst, C2)} || {C1, C2} <- CList],
            peel_loop(drop_tautologies(CList1), Fixed, Rounds - length(Batch))
    end.

%% Re-apply the constraint-split rule from clean_cons phase 1.5. peel_loop's
%% substitutions can re-introduce a top-level union on the LHS (or top-level
%% intersection on the RHS) by inlining a variable's lower bound that is
%% itself a union. Without this pass, a single `union(B1..B23) <: T`
%% constraint stays as one BDD with 23 cube atoms and becomes a 3^23
%% tensor-product explosion during normalize. Re-splitting it gives 23 cheap
%% per-arm constraints that partition cleanly along the per-arm variables.
resplit_unions(CList) ->
    lists:flatmap(
      fun({S, T}) ->
          S1 = simplify_ty(S),
          T1 = simplify_ty(T),
          LHSs = case S1 of
                     {union, A1} when length(A1) > 1 -> A1;
                     _ -> [S1]
                 end,
          RHSs = case T1 of
                     {intersection, A2} when length(A2) > 1 -> A2;
                     _ -> [T1]
                 end,
          [{L, R} || L <- LHSs, R <- RHSs]
      end, CList).

%% Drop trivially-true subtype constraints:
%%   * C <: C — identical sides (handled by `L =/= R`)
%%   * _ <: {predef, any} — RHS is universal top
%%   * {predef, none} <: _ — LHS is universal bottom
%%   * also any/none synonyms via {predef_alias, term}
%% Removing trivial constraints reduces partition coupling: a variable that
%% appeared only in trivial constraints now disappears from the partition.
drop_tautologies(CList) ->
    [C || {L, R} = C <- CList,
          L =/= R,
          not is_top(R),
          not is_bottom(L),
          not lhs_member_of_rhs_union(L, R)].

%% True iff L is structurally one of the arms of a union/intersection on the
%% RHS — `L <: union([..., L, ...])` is trivially satisfied since L is one of
%% the alternatives.
lhs_member_of_rhs_union(L, {union, Args}) -> lists:member(L, Args);
lhs_member_of_rhs_union(_, _) -> false.

%% Structural type simplification (top-down).
%% intersection: drop top arms (X ∩ any = X); if any arm is bottom, whole thing
%%   collapses to bottom. Singleton/empty cases.
%% union: drop bottom arms; if any arm is top, whole thing collapses to top.
%% Recurse into container types to simplify nested intersections/unions.
simplify_ty({intersection, Args0}) ->
    Args = [simplify_ty(A) || A <- Args0],
    case lists:any(fun is_bottom/1, Args) of
        true -> {predef, none};
        false ->
            case [A || A <- Args, not is_top(A)] of
                []  -> {predef, any};
                [X] -> X;
                Xs  ->
                    %% Distribute over the FIRST union arm (if any). This is
                    %% the standard `(A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C)` law and
                    %% it crucially exposes a top-level union to the
                    %% clean_cons constraint-splitter — otherwise an
                    %% `intersection([union, tuple_any]) <: T` constraint
                    %% would stay as a single huge BDD instead of becoming N
                    %% per-arm constraints. The case-clause typer commonly
                    %% emits exactly this `intersection(union_of_branches,
                    %% tuple_any)` shape during exhaustiveness checking.
                    case lists:splitwith(fun({union, _}) -> false; (_) -> true end, Xs) of
                        {Before, [{union, UArgs} | After]} when length(UArgs) > 1 ->
                            Other = Before ++ After,
                            simplify_ty({union,
                                [{intersection, [A | Other]} || A <- UArgs]});
                        _ ->
                            {intersection, Xs}
                    end
            end
    end;
simplify_ty({union, Args0}) ->
    Args = [simplify_ty(A) || A <- Args0],
    case lists:any(fun is_top/1, Args) of
        true -> {predef, any};
        false ->
            case [A || A <- Args, not is_bottom(A)] of
                []  -> {predef, none};
                [X] -> X;
                Xs  -> {union, Xs}
            end
    end;
simplify_ty({tuple, Args}) -> {tuple, [simplify_ty(A) || A <- Args]};
simplify_ty({cons, A, B}) -> {cons, simplify_ty(A), simplify_ty(B)};
simplify_ty({list, A}) -> {list, simplify_ty(A)};
simplify_ty({nonempty_list, A}) -> {nonempty_list, simplify_ty(A)};
simplify_ty({improper_list, A, B}) -> {improper_list, simplify_ty(A), simplify_ty(B)};
simplify_ty({nonempty_improper_list, A, B}) -> {nonempty_improper_list, simplify_ty(A), simplify_ty(B)};
simplify_ty({fun_full, Args, Ret}) -> {fun_full, [simplify_ty(A) || A <- Args], simplify_ty(Ret)};
simplify_ty({fun_any_arg, Ret}) -> {fun_any_arg, simplify_ty(Ret)};
simplify_ty({negation, T}) -> {negation, simplify_ty(T)};
simplify_ty({map, Assocs}) ->
    {map, [{K, simplify_ty(KK), simplify_ty(V)} || {K, KK, V} <- Assocs]};
simplify_ty({record, Name, Fields}) ->
    {record, Name, [{F, simplify_ty(T)} || {F, T} <- Fields]};
simplify_ty({named, Loc, Ref, Args}) ->
    {named, Loc, Ref, [simplify_ty(A) || A <- Args]};
simplify_ty(T) -> T.

%% Universally-top types only — `{tuple, [any, any]}` is the universal
%% *2-arity* tuple, not the universal type, so we must NOT mark it top.
is_top({predef, any}) -> true;
is_top({union, Args}) -> lists:any(fun is_top/1, Args);
is_top({intersection, Args}) -> lists:all(fun is_top/1, Args);
is_top(_) -> false.

is_bottom({predef, none}) -> true;
is_bottom({union, []}) -> true;
is_bottom({union, Args}) -> lists:all(fun is_bottom/1, Args);
is_bottom({intersection, Args}) -> lists:any(fun is_bottom/1, Args);
is_bottom(_) -> false.

%% Single-pass batch peelable discovery.
%%
%% Replaces the original `O(|V| * |C| * |ty|)` per-round scan (one
%% `classify_relaxed/2` walk over the full constraint list per variable) with
%% one shared `O(|C| * |ty|)` walk that records every non-Fixed variable's
%% (Uppers, Lowers, NestedPolarities) tuple. After the walk each variable is
%% classified locally using the same decision rule as `classify_relaxed_loop/5`.
%%
%% Returns a list of {V, Substitution} pairs, sorted by V so the resulting
%% peel order is deterministic.
-spec find_peelables([{ast:ty(), ast:ty()}], sets:set(ast:ty_varname())) ->
    [{ast:ty_varname(), ast:ty()}].
find_peelables(CList, Fixed) ->
    Data = collect_peel_data(CList, Fixed),
    %% Iterate in sorted V order so output is deterministic (matches the
    %% previous lists:sort(sets:to_list(...)) order).
    Sorted = lists:sort(maps:to_list(Data)),
    lists:foldr(
      fun({V, {Ups, Lows, NPols}}, Acc) ->
              case classify_peel_data(Ups, Lows, NPols) of
                  non_peelable -> Acc;
                  {peelable_lower, []} -> [{V, {predef, none}} | Acc];
                  {peelable_lower, [Single]} -> [{V, Single} | Acc];
                  {peelable_lower, Many} -> [{V, {union, Many}} | Acc];
                  {peelable_upper, []} -> [{V, {predef, any}} | Acc];
                  {peelable_upper, [Single]} -> [{V, Single} | Acc];
                  {peelable_upper, Many} -> [{V, {intersection, Many}} | Acc]
              end
      end, [], Sorted).

%% Same decision rule as `classify_relaxed_loop/5`'s terminal case.
classify_peel_data(_Ups, _Lows, NPols) when NPols =/= [] -> non_peelable; %% ABLATION: relaxed nested peel disabled
classify_peel_data(Ups, Lows, NPols) ->
    AllPol1 = lists:all(fun(P) -> P =:= 1 end, NPols),
    AllPol0 = lists:all(fun(P) -> P =:= 0 end, NPols),
    LowerBounds = lists:reverse(Lows),
    UpperBounds = dedup_keep_order(lists:reverse(Ups)),
    case {Ups, Lows, AllPol0, AllPol1} of
        {[],   [],   _, _}    -> non_peelable;
        {_,    [_|_], true,  _} -> {peelable_lower, LowerBounds};
        {[_|_], [], _,  true}   -> {peelable_upper, UpperBounds};
        {[],   [_|_], _, true}  -> {peelable_lower, LowerBounds};
        {[_|_], [_|_], _, true} -> {peelable_upper, UpperBounds};
        {[_|_], [], true, _}    -> {peelable_upper, UpperBounds};
        _ -> non_peelable
    end.

%% Walk every constraint exactly once, populating #{V => {Ups, Lows, NPols}}
%% for every non-Fixed variable that appears anywhere. Mirrors the per-V
%% logic in `classify_relaxed_loop/5`:
%%   - C1 = {var, V1} (top-LHS):  V1 gets C2 added to Ups; C1's only var
%%     occurrence is the top one, so don't add anything for V1 from C1.
%%   - C2 = {var, V2} (top-RHS):  V2 gets C1 added to Lows; same.
%%   - For each non-top side, walk it and add the polarity multiset of every
%%     non-Fixed variable encountered to that variable's NPols.
collect_peel_data(CList, Fixed) ->
    lists:foldl(
      fun({C1, C2}, Acc) ->
              case C1 =:= C2 of
                  true -> Acc;
                  false ->
                      %% Direct-top occurrences contribute Ups/Lows.
                      Acc1 = case C1 of
                                 {var, V1} ->
                                     case sets:is_element(V1, Fixed) of
                                         true -> Acc;
                                         false -> add_upper(V1, C2, Acc)
                                     end;
                                 _ -> Acc
                             end,
                      Acc2 = case C2 of
                                 {var, V2} ->
                                     case sets:is_element(V2, Fixed) of
                                         true -> Acc1;
                                         false -> add_lower(V2, C1, Acc1)
                                     end;
                                 _ -> Acc1
                             end,
                      %% Nested polarity walk. Skip a side that is exactly a
                      %% top-level var — that occurrence is already accounted
                      %% for via Ups/Lows.
                      Acc3 = case C1 of
                                 {var, _} -> Acc2;
                                 _ -> walk_polarities(C1, 0, Fixed, Acc2)
                             end,
                      case C2 of
                          {var, _} -> Acc3;
                          _ -> walk_polarities(C2, 1, Fixed, Acc3)
                      end
              end
      end, #{}, CList).

add_upper(V, T, Acc) ->
    maps:update_with(V,
        fun({Ups, Lows, NPols}) -> {[T | Ups], Lows, NPols} end,
        {[T], [], []}, Acc).

add_lower(V, T, Acc) ->
    maps:update_with(V,
        fun({Ups, Lows, NPols}) -> {Ups, [T | Lows], NPols} end,
        {[], [T], []}, Acc).

add_pol(V, P, Acc) ->
    maps:update_with(V,
        fun({Ups, Lows, NPols}) -> {Ups, Lows, [P | NPols]} end,
        {[], [], [P]}, Acc).

%% Walk T at outer polarity Pol, recording each non-Fixed variable's polarity
%% into Acc. Variance handling mirrors `var_polarities_in/3`:
%%   * fun_full: arguments contravariant.
%%   * negation: flip.
%%   * union/intersection/list/cons/tuple: same polarity.
%%   * map / record (each field) / named: invariant. Mirroring the original,
%%     we collect inner polarities then add them AND their inversions.
walk_polarities({var, V}, Pol, Fixed, Acc) ->
    case sets:is_element(V, Fixed) of
        true -> Acc;
        false -> add_pol(V, Pol, Acc)
    end;
walk_polarities({predef, _}, _, _, Acc) -> Acc;
walk_polarities({predef_alias, _}, _, _, Acc) -> Acc;
walk_polarities({singleton, _}, _, _, Acc) -> Acc;
walk_polarities({range, _, _}, _, _, Acc) -> Acc;
walk_polarities({empty_list}, _, _, Acc) -> Acc;
walk_polarities({bitstring}, _, _, Acc) -> Acc;
walk_polarities({fun_simple}, _, _, Acc) -> Acc;
walk_polarities({tuple_any}, _, _, Acc) -> Acc;
walk_polarities({map_any}, _, _, Acc) -> Acc;
walk_polarities({mu_var, _}, _, _, Acc) -> Acc;
walk_polarities({fun_full, Args, Ret}, Pol, Fixed, Acc) ->
    Flipped = 1 - Pol,
    Acc1 = lists:foldl(
             fun(A, A0) -> walk_polarities(A, Flipped, Fixed, A0) end, Acc, Args),
    walk_polarities(Ret, Pol, Fixed, Acc1);
walk_polarities({fun_any_arg, Ret}, Pol, Fixed, Acc) ->
    walk_polarities(Ret, Pol, Fixed, Acc);
walk_polarities({tuple, Args}, Pol, Fixed, Acc) ->
    lists:foldl(fun(A, A0) -> walk_polarities(A, Pol, Fixed, A0) end, Acc, Args);
walk_polarities({union, Args}, Pol, Fixed, Acc) ->
    lists:foldl(fun(A, A0) -> walk_polarities(A, Pol, Fixed, A0) end, Acc, Args);
walk_polarities({intersection, Args}, Pol, Fixed, Acc) ->
    lists:foldl(fun(A, A0) -> walk_polarities(A, Pol, Fixed, A0) end, Acc, Args);
walk_polarities({negation, T}, Pol, Fixed, Acc) ->
    walk_polarities(T, 1 - Pol, Fixed, Acc);
walk_polarities({list, T}, Pol, Fixed, Acc) ->
    walk_polarities(T, Pol, Fixed, Acc);
walk_polarities({nonempty_list, T}, Pol, Fixed, Acc) ->
    walk_polarities(T, Pol, Fixed, Acc);
walk_polarities({cons, A, B}, Pol, Fixed, Acc) ->
    walk_polarities(B, Pol, Fixed, walk_polarities(A, Pol, Fixed, Acc));
walk_polarities({improper_list, A, B}, Pol, Fixed, Acc) ->
    walk_polarities(B, Pol, Fixed, walk_polarities(A, Pol, Fixed, Acc));
walk_polarities({nonempty_improper_list, A, B}, Pol, Fixed, Acc) ->
    walk_polarities(B, Pol, Fixed, walk_polarities(A, Pol, Fixed, Acc));
walk_polarities({map, Assocs}, Pol, Fixed, Acc) ->
    lists:foldl(
      fun({_Kind, K, U}, A0) ->
              Inner = walk_polarities(K, Pol, Fixed, #{}),
              Inner1 = walk_polarities(U, Pol, Fixed, Inner),
              merge_invariant(Inner1, A0)
      end, Acc, Assocs);
walk_polarities({record, _, Fields}, Pol, Fixed, Acc) ->
    lists:foldl(
      fun({_, T}, A0) -> walk_polarities(T, Pol, Fixed, A0) end, Acc, Fields);
walk_polarities({named, _, _, []}, _, _, Acc) -> Acc;
walk_polarities({named, _, _, Args}, Pol, Fixed, Acc) ->
    lists:foldl(
      fun(A, A0) ->
              Inner = walk_polarities(A, Pol, Fixed, #{}),
              merge_invariant(Inner, A0)
      end, Acc, Args);
walk_polarities({mu, _, T}, Pol, Fixed, Acc) ->
    walk_polarities(T, Pol, Fixed, Acc);
walk_polarities(_, _, _, Acc) -> Acc.

%% For each V found in Inner with NPols = Ps, add Ps and [1 - P || P <- Ps]
%% (their inversions) to Outer's NPols. Matches the doubling in
%% `var_polarities_in/3` for invariant positions.
merge_invariant(Inner, Outer) ->
    maps:fold(
      fun(V, {_, _, InnerNPols}, OuterAcc) ->
              Doubled = InnerNPols ++ [1 - P || P <- InnerNPols],
              maps:update_with(V,
                  fun({Ups, Lows, NPols}) -> {Ups, Lows, Doubled ++ NPols} end,
                  {[], [], Doubled}, OuterAcc)
      end, Outer, Inner).

%% True iff T contains a `{var, V}` occurrence for any V in VarSet.
type_has_any_var(T, VarSet) ->
    [] =/= utils:everything(
             fun({var, V}) when is_atom(V) ->
                     case sets:is_element(V, VarSet) of
                         true -> {ok, true};
                         false -> error
                     end;
                (_) -> error
             end, T).

dedup_keep_order(L) ->
    lists:foldl(fun(X, Acc) ->
        case lists:member(X, Acc) of
            true -> Acc;
            false -> Acc ++ [X]
        end
    end, [], L).

-type clean_mode() :: {clean, symtab:t()} | no_clean.

-spec apply(t(), ast:ty(), clean_mode()) -> ast:ty().
apply(Subst = {tally_subst, BaseSubst, Fixed}, T, CleanMode) ->
    U = apply_base(BaseSubst, T),
    Res =
        case CleanMode of
            {clean, SymTab} -> clean(U, Fixed, SymTab);
            no_clean -> U
        end,
    ?LOG_TRACE("subst:apply, T=~s, Subst=~s, U=~s, Res=~s",
        pretty:render_ty(T),
        pretty:render_subst(Subst),
        pretty:render_ty(U),
        pretty:render_ty(Res)),
    Res;
apply(S, T, _) -> apply_base(S, T).

-spec apply_base(base_subst(), ast:ty()) -> ast:ty().
apply_base(S, T) ->
    case T of
        {singleton, _} -> T;
        {bitstring} -> T;
        {bitstring, _, _} -> T;
        {empty_list} -> T;
        {empty_bitstring} -> T;
        {cons, A, B} -> {cons, apply_base(S, A), apply_base(S, B)};
        {bitstring_cons, A, B} -> {bitstring_cons, apply_base(S, A), apply_base(S, B)};
        {list, U} -> {list, apply_base(S, U)};
        {mu, V, U} -> {mu, V, apply_base(S, U)};
        {nonempty_list, U} -> {nonempty_list, apply_base(S, U)};
        {improper_list, U, V} -> {improper_list, apply_base(S, U), apply_base(S, V)};
        {nonempty_improper_list, U, V} -> {nonempty_improper_list, apply_base(S, U), apply_base(S, V)};
        {fun_simple} -> T;
        {fun_any_arg, U} -> {fun_any_arg, apply_base(S, U)};
        {fun_full, Args, U} -> {fun_full, apply_list(S, Args), apply_base(S, U)};
        {range, _, _} -> T;
        {map_any} -> T;
        {map, Assocs} ->
            {map, lists:map(fun({Kind, U, V}) -> {Kind, apply_base(S, U), apply_base(S, V)} end, Assocs)};
        {predef, _} -> T;
        {predef_alias, _} -> T;
        {record, Name, Fields} ->
            {record, Name,
             lists:map(fun({FieldName, U}) -> {FieldName, apply_base(S, U)} end, Fields)};
        {named, Loc, Ref, Args} ->
            {named, Loc, Ref, apply_list(S, Args)};
        {tuple_any} -> T;
        {tuple, Args} -> {tuple, apply_list(S, Args)};
        {mu_var, _} -> T;
        {var, Alpha} ->
            case maps:find(Alpha, S) of
                error -> {var, Alpha};
                {ok, U} -> U
            end;
        {union, Args} -> {union, apply_list(S, Args)};
        {intersection, Args} -> {intersection, apply_list(S, Args)};
        {negation, U} -> {negation, apply_base(S, U)}
    end.

-spec apply_list(base_subst(), [ast:ty()]) -> [ast:ty()].
apply_list(S, L) -> lists:map(fun(T) -> apply_base(S, T) end, L).

-spec extend(t(), ast:ty_varname(), ast:ty()) -> t().
extend({tally_subst, BaseSubst, Fixed}, Alpha, T) ->
    {tally_subst, extend(BaseSubst, Alpha, T), Fixed};
extend(BaseSubst, Alpha, T) ->
    maps:put(Alpha, T, BaseSubst).

-spec from_list([{ast:ty_varname(), ast:ty()}]) -> t().
from_list(L) -> maps:from_list(L).

-spec empty() -> t().
empty() -> #{}.

-spec mk_tally_subst(sets:set(ast:ty_varname()), base_subst()) -> tally_subst().
mk_tally_subst(Fixed, Base) -> {tally_subst, Base, Fixed}.

clean_type(Ty, Fix, SymTab) ->
    UnfoldedTy = ast_utils:unfold_ty(SymTab, Ty),
    VCache = compute_variance_cache(SymTab),
    VarPositions = collect_vars(UnfoldedTy, 0, #{}, Fix, VCache),

    NoVarsDnf = maps:fold(
        fun(VariableName, VariablePositions, Tyy) ->
            case lists:usort(VariablePositions) of
                [0] ->
                    % !a => none
                    %  a => none
                    % FIXME (SW, 2023-12-08): this has bad performance. Better build one substitution
                    % and apply it once.
                    R = apply_base(#{VariableName => {predef, none}}, Tyy),
                    R;
                [1] ->
                    apply_base(#{VariableName => {predef, any}}, Tyy);
                _ -> Tyy
            end
        end, Ty, VarPositions),

    Cleaned = NoVarsDnf,
    Cleaned.

%% Variance precomputation
%%
%% For every schema {ty_scheme, [V1..Vn], Body} stored in the symtab, we
%% compute a vector [v1..vn] where each vi describes how Vi is used in Body
%% after substitution:
%%
%% Each pass walks every schema body using
%% the previous pass's cache for nested {named, _, R', As} lookups; the
%% pass returns the new cache. Iteration stops when no schema's vector
%% changes. 
%% Termination is guaranteed because each entry can widen at most twice 
%% from unused -> co/contra -> inv.

%% co: covariant positions only
%% contra: contravariant positions only
%% inv: both
%% unused: never appears in any unfolded form
-type variance() :: co | contra | inv | unused.
-type variance_cache() :: #{ symtab_ty_key() => [variance()] }.
-type symtab_ty_key() :: {ty_key, atom(), atom(), arity()}.

-spec compute_variance_cache(symtab:t()) -> variance_cache().
compute_variance_cache(SymTab) ->
    Types = symtab:get_types(SymTab),
    Initial = maps:map(
        fun(_, {ty_scheme, Vars, _}) -> [unused || _ <- Vars] end,
        Types),
    variance_fixpoint(Initial, Types).

-spec variance_fixpoint(variance_cache(), map()) -> variance_cache().
variance_fixpoint(OldCache, Types) ->
    NewCache = maps:map(
        fun(_Key, {ty_scheme, Vars, Body}) ->
            VarNames = [VName || {VName, _Bound} <- Vars],
            [variance_walk(Body, VN, co, unused, OldCache) || VN <- VarNames]
        end, Types),
    case NewCache =:= OldCache of
        true  -> NewCache;
        false -> variance_fixpoint(NewCache, Types)
    end.

%% Returns the variance of V in Ty, given outer polarity Pol and accumulator
%% Acc (variance already collected for V). Nested {named, _, R, As} references
%% look up R's vector in Cache and walk each As[i] under the composed polarity.
-spec variance_walk(ast:ty() | {ty_hole}, ast:ty_varname(), co | contra,
                    variance(), variance_cache()) -> variance().
variance_walk(Body, V, Pol, Acc, Cache) ->
    Contributions = utils:everything(
        fun(T) -> variance_node(T, V, Pol, Cache) end,
        Body),
    lists:foldl(fun(P, X) -> merge_pol(X, P) end, Acc, Contributions).

-spec variance_node(any(), ast:ty_varname(), co | contra, variance_cache()) ->
    {ok, variance()} | error.
variance_node({var, V}, V, Pol, _Cache) ->
    {ok, Pol};
variance_node({fun_full, Args, Ret}, V, Pol, Cache) ->
    Flipped = flip_pol(Pol),
    ArgVar = lists:foldl(
        fun(A, X) -> merge_pol(X, variance_walk(A, V, Flipped, unused, Cache)) end,
        unused, Args),
    RetVar = variance_walk(Ret, V, Pol, unused, Cache),
    {ok, merge_pol(ArgVar, RetVar)};
variance_node({negation, T}, V, Pol, Cache) ->
    {ok, variance_walk(T, V, flip_pol(Pol), unused, Cache)};
variance_node({named, _Loc, Ref, As}, V, Pol, Cache) ->
    {ok, variance_named(Ref, As, V, Pol, Cache)};
variance_node(_, _V, _Pol, _Cache) ->
    error.

-spec variance_named(ast:ty_ref(), [ast:ty()], ast:ty_varname(),
                     co | contra, variance_cache()) -> variance().
variance_named(Ref, As, V, Pol, Cache) ->
    Variances = lookup_variances(Ref, Cache),
    lists:foldl(
        fun({VarI, A}, X) -> merge_pol(X, arg_variance(VarI, A, V, Pol, Cache)) end,
        unused, lists:zip(Variances, As)).

-spec arg_variance(variance(), ast:ty(), ast:ty_varname(), co | contra, variance_cache()) -> variance().
arg_variance(co, A, V, Pol, Cache) -> variance_walk(A, V, Pol, unused, Cache);
arg_variance(contra, A, V, Pol, Cache) -> variance_walk(A, V, flip_pol(Pol), unused, Cache);
arg_variance(inv, A, V, Pol, Cache) ->
    Co = variance_walk(A, V, Pol, unused, Cache),
    Contra = variance_walk(A, V, flip_pol(Pol), unused, Cache),
    merge_pol(Co, Contra);
arg_variance(unused, _A, _V, _Pol, _Cache) -> unused.

-spec lookup_variances(ast:ty_ref(), variance_cache()) -> [variance()].
lookup_variances(Ref, Cache) ->
    Key = canonicalize_ref(Ref),
    maps:get(Key, Cache).

-spec canonicalize_ref(ast:ty_ref()) -> symtab_ty_key().
canonicalize_ref({ty_ref, M, N, A})  -> {ty_key, M, N, A};
canonicalize_ref({ty_qref, M, N, A}) -> {ty_key, M, N, A}.

-spec flip_pol(co | contra) -> co | contra.
flip_pol(co) -> contra;
flip_pol(contra) -> co.

-spec merge_pol(variance(), variance()) -> variance().
merge_pol(unused, X) -> X;
merge_pol(X, unused) -> X;
merge_pol(X, X) -> X;
merge_pol(_, _) -> inv.

% Walks a list of subtype constraints; for each {C1, C2}, C1 is in covariant
% (CPos) and C2 in contravariant (1-CPos) position.
%% Thread the accumulator through recursive walks. Adding the same CPos to a
%% variable's position list is idempotent (`lists:uniq/1` dedups), so threading
%% gives the same result as the previous "fork-and-merge" pattern that
%% restarted from `Pos` at each branch and then `maps:merge_with`'d every
%% subtree. Avoids quadratic map-merge work on large unions/intersections.
collect_vars_clist(L, CPos, Pos, Fix, VCache) when is_list(L) ->
    lists:foldl(fun({C1, C2}, Acc) ->
        Acc1 = collect_vars(C1, CPos, Acc, Fix, VCache),
        collect_vars(C2, 1 - CPos, Acc1, Fix, VCache)
                end, Pos, L).

-spec collect_vars(ast:ty() | {ty_hole}, 0 | 1, #{ast:ty_varname() => [0 | 1]},
                   sets:set(ast:ty_varname()), variance_cache()) ->
    #{ast:ty_varname() => [0 | 1]}.
collect_vars(M = {map, _}, CPos, Pos, Fix, VCache) ->
    collect_vars(ty_parser:rewrite_map_to_representation(M), CPos, Pos, Fix, VCache);
collect_vars({K, Components}, CPos, Pos, Fix, VCache) when K == union; K == intersection; K == tuple ->
    lists:foldl(fun(Ty, P) -> collect_vars(Ty, CPos, P, Fix, VCache) end, Pos, Components);
collect_vars({fun_full, Components, Target}, CPos, Pos, Fix, VCache) ->
    P1 = lists:foldl(fun(Ty, P) -> collect_vars(Ty, 1 - CPos, P, Fix, VCache) end, Pos, Components),
    collect_vars(Target, CPos, P1, Fix, VCache);
collect_vars({fun_any_arg, Target}, CPos, Pos, Fix, VCache) ->
    collect_vars(Target, CPos, Pos, Fix, VCache);
collect_vars({negation, Ty}, CPos, Pos, Fix, VCache) -> collect_vars(Ty, 1 - CPos, Pos, Fix, VCache);
collect_vars({predef, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({predef_alias, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({singleton, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({range, _, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({_, any}, _CPos, Pos, _, _) -> Pos;
collect_vars({empty_list}, _CPos, Pos, _, _) -> Pos;
collect_vars({empty_bitstring}, _CPos, Pos, _, _) -> Pos;
collect_vars({bitstring}, _CPos, Pos, _, _) -> Pos;
collect_vars({bitstring, _, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({map_any}, _CPos, Pos, _, _) -> Pos;
collect_vars({tuple_any}, _CPos, Pos, _, _) -> Pos;
collect_vars({fun_simple}, _CPos, Pos, _, _) -> Pos;
collect_vars({mu_var, _Name}, _CPos, Pos, _, _) -> Pos;
collect_vars({ty_hole}, _CPos, Pos, _, _) -> Pos;
collect_vars({nonempty_improper_list, A, B}, CPos, Pos, Fix, VCache) ->
    collect_vars(B, CPos, collect_vars(A, CPos, Pos, Fix, VCache), Fix, VCache);
collect_vars({nonempty_list, A}, CPos, Pos, Fix, VCache) ->
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({list, A}, CPos, Pos, Fix, VCache) ->
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({mu, _MuVar, A}, CPos, Pos, Fix, VCache) -> % skip recursion variables
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({cons, A, B}, CPos, Pos, Fix, VCache) ->
    collect_vars(B, CPos, collect_vars(A, CPos, Pos, Fix, VCache), Fix, VCache);
collect_vars({bitstring_cons, A, B}, CPos, Pos, Fix, VCache) ->
    collect_vars(B, CPos, collect_vars(A, CPos, Pos, Fix, VCache), Fix, VCache);
collect_vars({improper_list, A, B}, CPos, Pos, Fix, VCache) ->
    collect_vars(B, CPos, collect_vars(A, CPos, Pos, Fix, VCache), Fix, VCache);
collect_vars({var, Name}, CPos, Pos, Fix, _VCache) ->
    case sets:is_element(Name, Fix) of
        true -> Pos;
        _ ->
            case Pos of
                #{Name := [CPos]} -> Pos;
                #{Name := [_, _]} -> Pos;
                #{Name := [Other]} when Other =/= CPos -> Pos#{Name := [0, 1]};
                _ -> Pos#{Name => [CPos]}
            end
    end;
collect_vars({named, _Loc, Ref, Args}, CPos, Pos, Fix, VCache) ->
    % Use precomputed per-parameter variance to walk each Arg with the right polarity.
    Variances = lookup_variances(Ref, VCache),
    lists:foldl(
        fun({co,     A}, P) -> collect_vars(A, CPos,     P,  Fix, VCache);
           ({contra, A}, P) -> collect_vars(A, 1 - CPos, P,  Fix, VCache);
           ({inv,    A}, P) ->
               P1 = collect_vars(A, CPos,     P,  Fix, VCache),
               collect_vars(A, 1 - CPos, P1, Fix, VCache);
           ({unused, _A}, P) -> P
        end, Pos, lists:zip(Variances, Args));
collect_vars({record, _Name, Fields}, CPos, Pos, Fix, VCache) ->
    lists:foldl(
        fun({_FieldName, T}, P) -> collect_vars(T, CPos, P, Fix, VCache) end,
        Pos, Fields);
collect_vars(Ty, _, _, _, _) ->
    logger:error("Unhandled collect vars branch: ~p", [Ty]),
    errors:bug("Unhandled collect vars branch: ~p", [Ty]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

%% Build a tiny fake `ty_env` map for variance tests:
%%   schemas :: [{Name :: atom(), Vars :: [atom()], Body :: ast:ty()}]
%% Each Name becomes the {ty_key, test, Name, length(Vars)} key.
mk_test_types(Schemas) ->
    maps:from_list(
        [{{ty_key, test, Name, length(Vs)},
          {ty_scheme,
           [{V, {predef, any}} || V <- Vs],
           Body}}
         || {Name, Vs, Body} <- Schemas]).

run_variance_fp(Schemas) ->
    Types = mk_test_types(Schemas),
    Initial = maps:map(
        fun(_, {ty_scheme, Vars, _}) -> [unused || _ <- Vars] end,
        Types),
    variance_fixpoint(Initial, Types).

get_v(Name, Arity, Cache) ->
    maps:get({ty_key, test, Name, Arity}, Cache).

nref(Name, Args) ->
    {named, {loc, "test", 0, 0}, {ty_ref, test, Name, length(Args)}, Args}.

variance_co_test() ->
    %% F(A) = {A, F(A)} 
    %% A is co
    Body = {tuple, [{var, 'A'}, nref('F', [{var, 'A'}])]},
    Cache = run_variance_fp([{'F', ['A'], Body}]),
    ?assertEqual([co], get_v('F', 1, Cache)).

variance_inv_via_funarg_test() ->
    %% F(A) = {A, fun(F(A) -> B)} 
    %% A is inv
    Body = {tuple,
            [{var, 'A'},
             {fun_full, [nref('F', [{var, 'A'}])], {predef, atom}}]},
    Cache = run_variance_fp([{'F', ['A'], Body}]),
    ?assertEqual([inv], get_v('F', 1, Cache)).

variance_unused_test() ->
    %% F(A) = fun(F(A) -> ok)
    %% A is unused
    Body = {fun_full, [nref('F', [{var, 'A'}])], {singleton, ok}},
    Cache = run_variance_fp([{'F', ['A'], Body}]),
    ?assertEqual([unused], get_v('F', 1, Cache)).

variance_inv_self_ret_test() ->
    %% F(A) = fun(F(A) -> A)
    %% A is inv
    Body = {fun_full, [nref('F', [{var, 'A'}])], {var, 'A'}},
    Cache = run_variance_fp([{'F', ['A'], Body}]),
    ?assertEqual([inv], get_v('F', 1, Cache)).

variance_co_through_contra_test() ->
    %% G(A) = fun(A -> ok),  F(A) = fun(G(A) -> ok) 
    %% F's A is co
    BodyG = {fun_full, [{var, 'A'}], {singleton, ok}},
    BodyF = {fun_full, [nref('G', [{var, 'A'}])], {singleton, ok}},
    Cache = run_variance_fp([{'G', ['A'], BodyG}, {'F', ['A'], BodyF}]),
    ?assertEqual([contra], get_v('G', 1, Cache)),
    ?assertEqual([co], get_v('F', 1, Cache)).

variance_contra_through_co_test() ->
    %% G(A) = fun(A -> ok),  F(A) = G(A) 
    %% F's A is contra
    BodyG = {fun_full, [{var, 'A'}], {singleton, ok}},
    BodyF = nref('G', [{var, 'A'}]),
    Cache = run_variance_fp([{'G', ['A'], BodyG}, {'F', ['A'], BodyF}]),
    ?assertEqual([contra], get_v('G', 1, Cache)),
    ?assertEqual([contra], get_v('F', 1, Cache)).

variance_list_test() ->
    %% list(T) = empty_list() | cons(T, list(T))
    %% T is co
    Body = {union, [{empty_list}, {cons, {var, 'T'}, nref('list', [{var, 'T'}])}]},
    Cache = run_variance_fp([{'list', ['T'], Body}]),
    ?assertEqual([co], get_v('list', 1, Cache)).

-endif.

