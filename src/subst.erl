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

    [{Apply(C1), Apply(C2)} || {C1, C2} <- CList].

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
        % TODO full bitstring support
        {bitstring} -> T;
        % {binary, _, _} -> T;
        {empty_list} -> T;
        {cons, A, B} -> {cons, apply_base(S, A), apply_base(S, B)};
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


combine_vars(_K, V1, V2) ->
    lists:uniq(V1 ++ V2).

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
collect_vars_clist(L, CPos, Pos, Fix, VCache) when is_list(L) ->
    lists:foldl(fun({C1, C2}, Acc) ->
        M1 = collect_vars(C1, CPos, Acc, Fix, VCache),
        M2 = collect_vars(C2, 1-CPos, Acc, Fix, VCache),
        maps:merge_with(fun combine_vars/3, M1, M2)
                end, Pos, L).

-spec collect_vars(ast:ty() | {ty_hole}, 0 | 1, #{ast:ty_varname() => [0 | 1]},
                   sets:set(ast:ty_varname()), variance_cache()) ->
    #{ast:ty_varname() => [0 | 1]}.
collect_vars(M = {map, _}, CPos, Pos, Fix, VCache) ->
    collect_vars(ty_parser:rewrite_map_to_representation(M), CPos, Pos, Fix, VCache);
collect_vars({K, Components}, CPos, Pos, Fix, VCache) when K == union; K == intersection; K == tuple ->
    VPos = lists:map(fun(Ty) -> collect_vars(Ty, CPos, Pos, Fix, VCache) end, Components),
    lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, Pos, VPos);
collect_vars({fun_full, Components, Target}, CPos, Pos, Fix, VCache) ->
    VPos = lists:map(fun(Ty) -> collect_vars(Ty, 1 - CPos, Pos, Fix, VCache) end, Components),
    M1 = lists:foldl(fun(FPos, Current) -> maps:merge_with(fun combine_vars/3, FPos, Current) end, Pos, VPos),
    M2 = collect_vars(Target, CPos, Pos, Fix, VCache),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({negation, Ty}, CPos, Pos, Fix, VCache) -> collect_vars(Ty, 1 - CPos, Pos, Fix, VCache);
collect_vars({predef, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({predef_alias, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({singleton, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({range, _, _}, _CPos, Pos, _, _) -> Pos;
collect_vars({_, any}, _CPos, Pos, _, _) -> Pos;
collect_vars({empty_list}, _CPos, Pos, _, _) -> Pos;
collect_vars({bitstring}, _CPos, Pos, _, _) -> Pos;
collect_vars({map_any}, _CPos, Pos, _, _) -> Pos;
collect_vars({tuple_any}, _CPos, Pos, _, _) -> Pos;
collect_vars({fun_simple}, _CPos, Pos, _, _) -> Pos;
collect_vars({mu_var, _Name}, _CPos, Pos, _, _) -> Pos;
collect_vars({ty_hole}, _CPos, Pos, _, _) -> Pos;
collect_vars({nonempty_improper_list, A, B}, CPos, Pos, Fix, VCache) ->
    M1 = collect_vars(A, CPos, Pos, Fix, VCache),
    M2 = collect_vars(B, CPos, Pos, Fix, VCache),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({nonempty_list, A}, CPos, Pos, Fix, VCache) ->
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({list, A}, CPos, Pos, Fix, VCache) ->
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({mu, _MuVar, A}, CPos, Pos, Fix, VCache) -> % skip recursion variables
    collect_vars(A, CPos, Pos, Fix, VCache);
collect_vars({cons, A, B}, CPos, Pos, Fix, VCache) ->
    M1 = collect_vars(A, CPos, Pos, Fix, VCache),
    M2 = collect_vars(B, CPos, Pos, Fix, VCache),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({improper_list, A, B}, CPos, Pos, Fix, VCache) ->
    M1 = collect_vars(A, CPos, Pos, Fix, VCache),
    M2 = collect_vars(B, CPos, Pos, Fix, VCache),
    maps:merge_with(fun combine_vars/3, M1, M2);
collect_vars({var, Name}, CPos, Pos, Fix, _VCache) ->
    Z = case sets:is_element(Name, Fix) of
        true -> Pos;
        _ ->
            AllPositions = maps:get(Name, Pos, []),
            Pos#{Name => lists:uniq(AllPositions ++ [CPos])}
    end,
    Z;
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

