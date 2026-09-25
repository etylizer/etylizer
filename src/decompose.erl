-module(decompose).

% Decompose constraints similar to what tally does, before tally, with side-constraints.
% Allows cleaning to clean more variables.
%
%     S1 | S2 <: T          ==  S1 <: T, S2 <: T
%     S <: T1 /\ T2         ==  S <: T1, S <: T2
%     S <: {T1, .., Tn}     ==  M1 <: T1, .., Mn <: Tn  for every non-empty product {M1, .., Mn} of S
%     S <: [H @ R]          ==  M1 <: H, M2 <: R        for every non-empty product [M1 @ M2] of S
%     list(A) <: list(B)    ==  A <: B                  if A is non-empty
%     /\ (Pi -> Ri) <: A -> B  ==  A <: Pj, Rj <: B     if A is non-empty and overlaps Pj only
%     #{K1 => V1} <: #{K2 => V2}  ==  K1 <: K2, V1 <: V2  if K1 and V1 are non-empty

-export([step/3]).

-include("metrics.hrl").

-export_type([constraints/0]).

-type constraints() :: [{ast:ty(), ast:ty()}].
-type lower_bounds() :: #{ast:ty_varname() => [ast:ty()]}.
-record(ctx, { 
    lower_bounds :: lower_bounds(), 
    mono :: etally:monomorphic_variables(), 
    symtab :: symtab:t()
}).
-type ctx() :: #ctx{}.
% the n-tuples, or the cons cells with their head and tail
-type shape() :: {tuple, non_neg_integer()} | cons.
-type product() :: [ast:ty()].

% one pass over the constraints
-spec step(constraints(), sets:set(ast:ty_varname()), symtab:t()) -> constraints().
step(Cons, Fixed, SymTab) ->
    ty_parser:set_symtab(SymTab),
    Mono = maps:from_list([{ty_variable:new_with_name(V), []} || V <- sets:to_list(Fixed)]),
    Ctx = #ctx{lower_bounds = lower_bounds(Cons, Fixed), mono = Mono, symtab = SymTab},
    lists:flatmap(fun(C) -> rule(C, Ctx) end, Cons).

-spec lower_bounds(constraints(), sets:set(ast:ty_varname())) -> lower_bounds().
lower_bounds(Cons, Fixed) ->
    maps:groups_from_list(fun({_, {var, V}}) -> V end, fun({L, _}) -> L end,
        [C || C = {_, {var, V}} <- Cons, is_atom(V), not sets:is_element(V, Fixed)]).

-spec rule({ast:ty(), ast:ty()}, ctx()) -> constraints().
rule(C = {S, T}, Ctx) ->
    case {S, T} of
        {_, {intersection, Ts}} -> [{S, Ti} || Ti <- Ts];
        {{union, Ss}, _} -> [{Si, T} || Si <- Ss];
        {_, {tuple, Ts}} -> products(C, {tuple, length(Ts)}, Ts, Ctx);
        {_, {cons, H, R}} -> products(C, cons, [H, R], Ctx);
        {_, {nonempty_list, B}} -> products(C, cons, [B, {list, B}], Ctx);
        {{empty_list}, {list, _}} -> [];     % [] is in every list type
        {{list, A}, {list, B}} -> if_nonempty([A], [{A, B}], C, Ctx);
        {{intersection, [{list, A}, {negation, {empty_list}}]}, {list, B}} ->
            % list(A) /\ not([]) is nonempty_list(A)
            if_nonempty([A], [{A, B}], C, Ctx);
        {{named, Loc, Ref, Args}, {list, _}} ->
            % a named list type is its body
            case ast_utils:unfold_named(Ctx#ctx.symtab, Ref, Args, Loc) of
                U = {list, _} -> rule({U, T}, Ctx);
                U = {nonempty_list, _} -> rule({U, T}, Ctx);
                _ -> [C]
            end;
        {_, {list, B}} -> products(C, cons, [B, T], Ctx);
        {_, {fun_full, As, B}} -> arrow(C, As, B, Ctx);
        {{map, [{map_field_opt, K1, V1}]}, {map, [{map_field_opt, K2, V2}]}} ->
            if_nonempty([K1, V1], [{K1, K2}, {V1, V2}], C, Ctx);
        _ -> [C]
    end.

-spec if_nonempty([ast:ty()], constraints(), {ast:ty(), ast:ty()}, ctx()) -> constraints().
if_nonempty(Conditions, Decomposed, Original, Ctx) ->
    case lists:all(fun(X) -> nonempty(X, Ctx) end, Conditions) of
        true ->
            ?METRIC_COUNT(rule, element(1, element(2, Original))),
            Decomposed;
        false -> [Original]
    end.

% S <: {T1, .., Tn} or S <: [T1 @ T2], for an S made of values of the shape.
-spec products({ast:ty(), ast:ty()}, shape(), [ast:ty()], ctx()) -> constraints().
products(C = {S, _}, Shape, Ts, Ctx) ->
    case of_shape(S, Shape) andalso members(S, Shape, Ctx, []) of
        {ok, Ms} ->
            Empty = fun(X) -> subty:is_subty(Ctx#ctx.symtab, X, {predef, none}) end,
            NonEmpty = [M || M <- Ms, not lists:any(Empty, M)],
            if_nonempty(lists:append(NonEmpty), lists:usort([B || M <- NonEmpty, B <- lists:zip(M, Ts)]), C, Ctx);
        _ -> [C]
    end.

-spec arrow({ast:ty(), ast:ty()}, [ast:ty()], ast:ty(), ctx()) -> constraints().
arrow(C = {S, _}, As, B, Ctx) ->
    Clauses = case S of {intersection, Fs} -> Fs; _ -> [S] end,
    IsClause = fun({fun_full, Ps, _}) -> length(Ps) =:= length(As); (_) -> false end,
    Disjoint = fun(Ps) -> lists:any(fun({A, P}) -> disjoint(A, P, Ctx) end, lists:zip(As, Ps)) end,
    case lists:all(IsClause, Clauses) andalso [F || F = {fun_full, Ps, _} <- Clauses, not Disjoint(Ps)] of
        [{fun_full, Ps, R}] -> if_nonempty(As, lists:zip(As, Ps) ++ [{R, B}], C, Ctx);
        _ -> [C]
    end.

-spec of_shape(ast:ty(), shape()) -> boolean().
of_shape({tuple, Cs}, {tuple, N}) -> length(Cs) =:= N;
of_shape({cons, _, _}, cons) -> true;
of_shape({nonempty_list, _}, cons) -> true;
of_shape({intersection, Ss}, Shape) -> lists:any(fun(X) -> of_shape(X, Shape) end, Ss);
of_shape(_, _) -> false.

-spec anys(shape()) -> product().
anys({tuple, N}) -> lists:duplicate(N, {predef, any});
anys(cons) -> [{predef, any}, {predef, any}].

-spec any_of(shape()) -> ast:ty().
any_of(Shape = {tuple, _}) -> {tuple, anys(Shape)};
any_of(cons) -> {cons, {predef, any}, {predef, any}}.

% The values of the shape in a type, as a union of products. 
% Named types are unfolded, unless one unfolds to itself
-spec members(ast:ty(), shape(), ctx(), [ast:ty()]) -> {ok, [product()]} | none.
members({tuple, Cs}, {tuple, N}, _, _) when length(Cs) =:= N -> {ok, [Cs]};
members({cons, H, R}, cons, _, _) -> {ok, [[H, R]]};
members({nonempty_list, A}, cons, _, _) -> {ok, [[A, {list, A}]]};
members({list, A}, cons, _, _) -> {ok, [[A, {list, A}]]};   % [] is no cons cell
members({union, Us}, Shape, Ctx, Seen) ->
    case all_ok([members(U, Shape, Ctx, Seen) || U <- Us]) of
        {ok, Mss} -> {ok, lists:append(Mss)};
        none -> none
    end;
members({intersection, Xs}, Shape, Ctx, Seen) ->
    % the cartesian meet of the positive parts, less the negated ones
    {Negs, Pos} = lists:partition(fun(X) -> element(1, X) =:= negation end, Xs),
    case {all_ok([members(X, Shape, Ctx, Seen) || X <- Pos]), all_ok([members(X, Shape, Ctx, Seen) || {negation, X} <- Negs])} of
        {{ok, PosMss}, {ok, NegMss}} ->
            Meet = fun(M1, M2) -> [ast_lib:mk_intersection([A, B]) || {A, B} <- lists:zip(M1, M2)] end,
            Ms = lists:foldl(fun(Ms2, Ms1) -> [Meet(M1, M2) || M1 <- Ms1, M2 <- Ms2] end, [anys(Shape)], PosMss),
            subtract(Ms, lists:append(NegMss), Ctx);
        _ -> none
    end;
members(T = {named, Loc, Ref, Args}, Shape, Ctx, Seen) ->
    case lists:member(T, Seen) of
        true -> none;
        false -> members(ast_utils:unfold_named(Ctx#ctx.symtab, Ref, Args, Loc), Shape, Ctx, [T | Seen])
    end;
members(T, Shape, Ctx, _) ->
    % a type of any other syntax either misses the values of the shape
    % entirely, or contains all of them, or is left alone
    case disjoint(T, any_of(Shape), Ctx) of
        true -> {ok, []};
        false ->
            case subty:is_subty(Ctx#ctx.symtab, any_of(Shape), T) of
                true -> {ok, [anys(Shape)]};
                false -> none
            end
    end.

-spec all_ok([{ok, A} | none]) -> {ok, [A]} | none.
all_ok(Rs) ->
    case lists:member(none, Rs) of
        true -> none;
        false -> {ok, [R || {ok, R} <- Rs]}
    end.

% The products minus the negated ones
-spec subtract([product()], [product()], ctx()) -> {ok, [product()]} | none.
subtract(Ms, [], _) -> {ok, Ms};
subtract(Ms, [N | Ns], Ctx) ->
    Less = fun(M) ->
        Zipped = lists:zip(M, N),
        case lists:any(fun({A, B}) -> disjoint(A, B, Ctx) end, Zipped) of
            true -> {ok, [M]};
            false ->
                case [AB || AB = {A, B} <- Zipped, not subty:is_subty(Ctx#ctx.symtab, A, B)] of
                    [] -> {ok, []};
                    [Out] -> {ok, [[case AB of Out -> ast_lib:mk_diff(A, B); _ -> A end || AB = {A, B} <- Zipped]]};
                    _ -> none
                end
        end
    end,
    case all_ok([Less(M) || M <- Ms]) of
        {ok, Mss} -> subtract(lists:append(Mss), Ns, Ctx);
        none -> none
    end.

-spec nonempty(ast:ty(), ctx()) -> boolean().
nonempty(T, #ctx{lower_bounds = LBs, mono = Mono}) ->
    Cons = [{T, {predef, none}} | bounds(sets:to_list(tyutils:free_in_ty(T)), LBs, [])],
    not etally:is_tally_satisfiable([{ty_parser:parse(S), ty_parser:parse(U)} || {S, U} <- Cons], Mono).

% the lower bounds of the variables and nested variables
-spec bounds([ast:ty_varname()], lower_bounds(), constraints()) -> constraints().
bounds([], _, Acc) -> Acc;
bounds([V | Vs], LBs, Acc) ->
    Ls = maps:get(V, LBs, []),
    More = lists:flatmap(fun(L) -> sets:to_list(tyutils:free_in_ty(L)) end, Ls),
    bounds(More ++ Vs, maps:remove(V, LBs), [{L, {var, V}} || L <- Ls] ++ Acc).

-spec disjoint(ast:ty(), ast:ty(), ctx()) -> boolean().
disjoint(A, B, #ctx{symtab = SymTab}) ->
    subty:is_subty(SymTab, ast_lib:mk_intersection([A, B]), {predef, none}).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

step_test() ->
    global_state:with_new_state(fun() ->
        A = {var, 'A'}, B = {var, 'B'}, V = {var, 'V'},
        Int = stdtypes:tint(), Atom = stdtypes:tatom(), Any = {predef, any},
        Step = fun(Cs) -> step(Cs, sets:new(), symtab:empty()) end,
        % splits need no side condition
        [{Int, A}, {Atom, A}] = Step([{{union, [Int, Atom]}, A}]),
        [{A, Int}, {A, Atom}] = Step([{A, {intersection, [Int, Atom]}}]),
        % ground components are non-empty
        [{Atom, B}, {Int, A}] = Step([{{tuple, [Int, Atom]}, {tuple, [A, B]}}]),
        % a variable component needs a non-empty lower bound
        Stuck = [{{tuple, [V, Atom]}, {tuple, [A, B]}}],
        Stuck = Step(Stuck),
        [{Int, V}, {Atom, B}, {V, A}] = Step([{Int, V} | Stuck]),
        % an empty product is below everything
        [] = Step([{{tuple, [{predef, none}, Atom]}, {tuple, [A, B]}}]),
        % intersections of tuples are met componentwise first
        [{Int, A}] = Step([{{intersection, [{tuple, [Int]}, {tuple, [Any]}]}, {tuple, [A]}}]),
        % the arrow arguments of the expected type bound the parameters, the
        % body the result 
        % an argument variable needs a non-empty lower bound
        Lam = {fun_full, [A, B], {tuple, [A, B]}},
        Expected = {fun_full, [Int, V], V},
        [{Int, A}, {V, B}, {{tuple, [A, B]}, V}] = Step([{Lam, Expected}, {Atom, V}]) -- [{Atom, V}],
        StuckArrow = [{Lam, Expected}],
        StuckArrow = Step(StuckArrow),
        % an overloaded function where the clause the arguments overlap
        Over = {intersection, [{fun_full, [Int], Int}, {fun_full, [Atom], Atom}]},
        [{{singleton, 1}, Int}, {Int, A}] = Step([{Over, {fun_full, [{singleton, 1}], A}}]),
        StuckOver = [{Over, {fun_full, [V], A}}],
        StuckOver = Step(StuckOver),
        % a union of tuples on the left minus the negated pattern
        % every product left bounds the pattern variables by its components
        Scrut = {intersection, [{union, [{tuple, [{singleton, a}, Int]}, {tuple, [{singleton, b}, Atom]}]},
                                {tuple, [Any, Any]},
                                {negation, {tuple, [{singleton, a}, Any]}}]},
        [{Atom, A}, {{singleton, b}, Any}] = Step([{Scrut, {tuple, [Any, A]}}]),
        % a variable on the left
        Var = [{{intersection, [V, {tuple, [Any]}]}, {tuple, [A]}}],
        Var = Step(Var),
        % maps where an empty key or value domain would leave the empty map only
        Map = fun(K, Val) -> {map, [{map_field_opt, K, Val}]} end,
        [{Int, A}, {Atom, B}] = Step([{Map(Int, Atom), Map(A, B)}]),
        StuckMap = [{Map(V, Atom), Map(A, B)}],
        StuckMap = Step(StuckMap),
        [{Int, V}, {V, A}, {Atom, B}] = Step([{Int, V} | StuckMap]),
        % a ground list pattern binds head and tail
        L3 = {intersection, [{cons, Atom, {cons, Int, {empty_list}}}, {cons, Any, Any}]},
        [{Atom, A}, {{cons, Int, {empty_list}}, B}] = Step([{L3, {cons, A, B}}]),
        % lists and conses
        [{Int, A}] = Step([{{list, Int}, {list, A}}]),
        [{{empty_list}, {list, A}}, {Int, A}] = Step([{{cons, Int, {empty_list}}, {list, A}}]),
        ok
    end).

-endif.
