-module(ast_lib).

% @doc This header file defines type specifications for our internal AST. It is
% heavily derived from the erlang ast (defined in ast_erl.erl). See the README for
% a description of the properties of the internal AST.

-export([simplify/1, reset/0, ast_to_erlang_ty/1, erlang_ty_to_ast/1, ast_to_erlang_ty_var/1, erlang_ty_var_to_var/1]).
-define(VAR_ETS, ast_norm_var_memo). % remember variable name -> variable ID to convert variables properly

-export([mk_intersection/1, mk_union/1, mk_negation/1, mk_diff/2]).

reset() ->
    catch ets:delete(?VAR_ETS),
    erlang:put(ty_asy_cache, #{}),
    ets:new(?VAR_ETS, [public, named_table]).

unfold_intersection([], All) -> All;
unfold_intersection([{intersection, Components} | Rest], All) ->
    unfold_intersection(Components ++ Rest, All);
unfold_intersection([X | Rest], All) ->
    unfold_intersection(Rest, All ++ [X]) .

unfold_union([], All) -> All;
unfold_union([{union, Components} | Rest], All) ->
    unfold_union(Components ++ Rest, All);
unfold_union([X | Rest], All) ->
    unfold_union(Rest, All ++ [X]) .

% smart constructors for intersection, union and negation
-spec mk_intersection([ast:ty()]) -> ast:ty().
mk_intersection(Tys) ->
    HasEmpty =
        lists:any(
            fun(T) ->
                case T of
                    {predef, none} -> true;
                    {negation, {predef, any}} -> true;
                    _ -> false
                end
            end,
            Tys),
    case HasEmpty of
        true -> {predef, none};
        _ ->
            Filtered =
                lists:filter(
                    fun(T) ->
                        case T of
                            [] -> false;
                            {predef, any} -> false;
                            {negation, {predef, none}} -> false;
                            _ -> true
                        end
                    end,
                    Tys),
            case Filtered of
                [] -> {predef, any};
                [T] -> T;
                _ -> {intersection, unfold_intersection(Filtered, [])}
            end
    end.

mk_diff(T1, T2) ->
   mk_intersection([T1, mk_negation(T2)]).

-spec mk_union([ast:ty()]) -> ast:ty().
mk_union(Tys) ->
    HasAny =
        lists:any(
            fun(T) ->
                case T of
                    {predef, any} -> true;
                    {negation, {predef, none}} -> true;
                    _ -> false
                end
            end,
            Tys),
    case HasAny of
        true -> {predef, any};
        _ ->
            Filtered =
                lists:filter(
                    fun(T) ->
                        case T of
                            {predef, none} -> false;
                            [] -> error(Tys);
                            _ -> true
                        end
                    end,
                    Tys),
            case Filtered of
                [] -> {predef, none};
                [T] -> T;
                _ -> {union, unfold_union(Filtered, [])}
            end
    end.

-spec mk_negation(ast:ty()) -> ast:ty().
mk_negation({predef, any}) -> {predef, none};
mk_negation({predef, none}) -> {predef, any};
mk_negation(T) -> {negation, T}.

erlang_ty_var_to_var({var, Id, Name}) ->
    Object = ets:lookup(?VAR_ETS, Name),
    case Object of
        % new variable not seen before!
        [] -> {var, list_to_atom("mu" ++ integer_to_list(Id))};
        [{_, _}] -> {var, Name}
    end.

erlang_ty_to_ast(X) ->
    Cache = erlang:get(ty_ast_cache),
    Cached = maps:get(X, Cache, undefined),
    {Pol, Full} = maybe_transform(Cached, X, Cache),
    case Pol of
        pos -> Full;
        neg -> stdtypes:tnegate(Full)
    end.

% Checks the cache before performing excessive transformations.
maybe_transform(undefined, X, Cache) ->
    V = ty_rec:transform(
        X,
        #{
            to_fun => fun(S, T) -> stdtypes:tfun_full(lists:map(fun(F) ->
                (erlang_ty_to_ast(F)) end,S),
                (erlang_ty_to_ast(T))
            ) end,
            to_tuple => fun(Ts) -> stdtypes:ttuple(lists:map(fun(T) -> (erlang_ty_to_ast(T)) end,Ts)) end,
            to_atom => fun(A) -> stdtypes:tatom(A) end,
            to_list => fun(A, B) -> stdtypes:tlist_improper((erlang_ty_to_ast(A)), (erlang_ty_to_ast(B))) end,
            to_int => fun(S, T) -> stdtypes:trange(S, T) end,
            to_predef => fun('[]') -> stdtypes:tempty_list(); (Predef) -> {predef, Predef} end,
            any_tuple => fun stdtypes:ttuple_any/0,
            any_tuple_i => fun(Size) -> stdtypes:ttuple([stdtypes:tany() || _ <- lists:seq(1, Size)]) end,
            any_function => fun stdtypes:tfun_any/0,
            any_function_i => fun(Size) -> stdtypes:tfun([stdtypes:tnone() || _ <- lists:seq(1, Size)], stdtypes:tany()) end,
            any_int => fun stdtypes:tint/0,
            any_list => fun stdtypes:tlist_any/0,
            any_atom => fun stdtypes:tatom/0,
            any_predef => fun stdtypes:tspecial_any/0,
            empty => fun stdtypes:tnone/0,
            any => fun stdtypes:tany/0,
            var => fun erlang_ty_var_to_var/1,
            diff => fun ast_lib:mk_diff/2,
            union => fun ast_lib:mk_union/1,
            intersect => fun ast_lib:mk_intersection/1,
            negate => fun ast_lib:mk_negation/1
        }),
    CacheNew = maps:put(X, V, Cache),
    put(ty_ast_cache, CacheNew),
    V;

maybe_transform(V, _, _) ->
    V.


simplify(Full) ->
%%    io:format(user, ">> Full~n~p~n", [Full]),
    (_Dnf = {union, Unions}) = dnf:to_dnf(dnf:to_nnf(Full)),
%%    io:format(user, ">> DNF~n~p~n", [_Dnf]),
    % filter empty intersections
    FilterEmpty = {union, lists:filter(fun(E) -> not ty_rec:is_empty(ast_to_erlang_ty(E)) end, Unions)},

    % for any variable, extract them
    E = ast_to_erlang_ty(FilterEmpty),
    {Enew, Extracted} = extract_variables(E, ty_rec:all_variables(E), []),
    Neww = case Enew of
        E -> FilterEmpty;
        _ -> erlang_ty_to_ast(Enew)
    end,

    R = mk_union([mk_union(Extracted), Neww]),
    ToReduce = dnf:to_dnf(dnf:to_nnf(R)),
    % reduce everything rigorously until there are no redundant parts in the type
    % a full reduce is very expensive
    reduce_until(ToReduce).

reduce_until(ToReduce) -> find_first_reduce(ToReduce, ToReduce, []).

find_first_reduce(_OriginalTy, {union, []}, OlderLines) -> {union, OlderLines};
find_first_reduce(OriginalTy, {union, [{intersection, Line} | Lines]}, OlderLines) ->
    WithoutLine = {union, Lines ++ OlderLines},
    case subty:is_equivalent(symtab:empty(), WithoutLine, OriginalTy) of % TODO symtab?
        true ->
            % is equivalent without the whole line
            find_first_reduce(OriginalTy, {union, Lines}, OlderLines);
        false ->
            ToReplaceLine = find_line_reduce(OriginalTy, {union, Lines ++ OlderLines}, {intersection, Line}, []),
            find_first_reduce(OriginalTy, {union, Lines}, [ToReplaceLine | OlderLines])
    end.

find_line_reduce(_OriginalTy, {union, _Lines}, {intersection, []}, OtherPartsOfLine) -> {intersection, OtherPartsOfLine};
find_line_reduce(OriginalTy, {union, Lines}, {intersection, [Atom | Atoms]}, OtherPartsOfLine) ->
    ReducedTry = {union, [{intersection, Atoms ++ OtherPartsOfLine} | Lines]},
    case subty:is_equivalent(symtab:empty(), ReducedTry, OriginalTy) of % TODO symtab?
        true ->
            find_line_reduce(OriginalTy, {union, Lines}, {intersection, Atoms}, OtherPartsOfLine);
        false ->
            find_line_reduce(OriginalTy, {union, Lines}, {intersection, Atoms}, [Atom | OtherPartsOfLine])
    end.


extract_variables(ETy, [], ExtractedVars) -> {ETy, ExtractedVars};
extract_variables(ETy, [Var | OtherVars], ExtractedVars) ->
    V = ty_rec:variable(Var),
    case ty_rec:is_subtype(V, ETy) of
        true ->
            % variable is in the type, diff and extract
            extract_variables(ty_rec:diff(ETy, V), OtherVars, [erlang_ty_var_to_var(Var) | ExtractedVars]);
        _ ->
            extract_variables(ETy, OtherVars, ExtractedVars)
    end.

ast_to_erlang_ty({singleton, Atom}) when is_atom(Atom) ->
    TyAtom = ty_atom:finite([Atom]),
    TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
    ty_rec:atom(TAtom);
ast_to_erlang_ty({singleton, IntOrChar}) ->
    Int = dnf_var_int:int(ty_interval:interval(IntOrChar, IntOrChar)),
    ty_rec:interval(Int);
% TODO
ast_to_erlang_ty({binary, _, _}) ->
    erlang:error("Bitstrings not implemented yet");

ast_to_erlang_ty({tuple_any}) ->
    ty_rec:tuple();
ast_to_erlang_ty({tuple, Comps}) when is_list(Comps)->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T) end, Comps),

    T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
    ty_rec:tuple(length(Comps), T);

% funs
ast_to_erlang_ty({fun_simple}) ->
    ty_rec:function();
ast_to_erlang_ty({fun_full, Comps, Result}) ->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T) end, Comps),
    TyB = ast_to_erlang_ty(Result),

    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, TyB))),
    ty_rec:function(length(Comps), T);

% var
ast_to_erlang_ty({var, A}) ->
    ty_rec:variable(maybe_new_variable(A));

% ty_some_list
ast_to_erlang_ty({list, Ty}) -> ty_rec:union( ast_to_erlang_ty({improper_list, Ty, {empty_list}}), ast_to_erlang_ty({empty_list}) );
ast_to_erlang_ty({nonempty_list, Ty}) -> ast_to_erlang_ty({nonempty_improper_list, Ty, {empty_list}});
ast_to_erlang_ty({nonempty_improper_list, Ty, Term}) -> ty_rec:diff(ast_to_erlang_ty({list, Ty}), ast_to_erlang_ty(Term));
ast_to_erlang_ty({improper_list, A, B}) ->
    ty_rec:list(dnf_var_ty_list:list(dnf_ty_list:list(ty_list:list(ast_to_erlang_ty(A), ast_to_erlang_ty(B)))));
ast_to_erlang_ty({empty_list}) ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef('[]')));
ast_to_erlang_ty({predef, T}) when T == pid; T == port; T == reference; T == float ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef(T)));

% named
ast_to_erlang_ty({named, _, _Ref, _Args}) ->
    erlang:error("named references not implemented yet");

% ty_predef_alias
ast_to_erlang_ty({predef_alias, Alias}) ->
    ast_to_erlang_ty(stdtypes:expand_predef_alias(Alias));

% ty_predef
ast_to_erlang_ty({predef, atom}) ->
    Atom = dnf_var_ty_atom:any(),
    ty_rec:atom(Atom);

ast_to_erlang_ty({predef, any}) -> ty_rec:any();
ast_to_erlang_ty({predef, none}) -> ty_rec:empty();
ast_to_erlang_ty({predef, integer}) ->
    ty_rec:interval();

% ints
ast_to_erlang_ty({range, From, To}) ->
    Int = dnf_var_int:int(ty_interval:interval(From, To)),
    ty_rec:interval(Int);

ast_to_erlang_ty({union, []}) -> ty_rec:empty();
ast_to_erlang_ty({union, [A]}) -> ast_to_erlang_ty(A);
ast_to_erlang_ty({union, [A|T]}) -> ty_rec:union(ast_to_erlang_ty(A), ast_to_erlang_ty({union, T}));

ast_to_erlang_ty({intersection, []}) -> ty_rec:any();
ast_to_erlang_ty({intersection, [A]}) -> ast_to_erlang_ty(A);
ast_to_erlang_ty({intersection, [A|T]}) -> ty_rec:intersect(ast_to_erlang_ty(A), ast_to_erlang_ty({intersection, T}));

ast_to_erlang_ty({negation, Ty}) -> ty_rec:negate(ast_to_erlang_ty(Ty));

ast_to_erlang_ty(T) ->
    erlang:error({"Norm not implemented or malformed type", T}).

ast_to_erlang_ty_var({var, Name}) when is_atom(Name) ->
    maybe_new_variable(Name).

maybe_new_variable(Name) ->
    Object = ets:lookup(?VAR_ETS, Name),
    case Object of
        [] ->
            Var = ty_variable:new(Name),
            ets:insert(?VAR_ETS, {Name, Var}),
            Var;
        [{_, Variable}] ->
            Variable
    end.
