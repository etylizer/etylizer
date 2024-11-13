-module(ast_lib).

-export([reset/0, simplify/2, ast_to_erlang_ty/1, ast_to_erlang_ty/2, raw_erlang_ty_to_ast/1, raw_erlang_ty_to_ast/2, erlang_ty_to_ast/1, erlang_ty_to_ast/2, ast_to_erlang_ty_var/1, erlang_ty_var_to_var/1]).

-export([
    mk_intersection/1,
    mk_intersection/2,
    mk_union/1,
    mk_union/2,
    mk_negation/1,
    mk_diff/2
]).

reset() ->
    erlang:put(ty_ast_cache, #{}),
    ok.

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
-spec mk_intersection(ast:ty(), ast:ty()) -> ast:ty().
mk_intersection(T1, T2) -> mk_intersection([T1, T2]).

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

-spec mk_union(ast:ty(), ast:ty()) -> ast:ty().
mk_union(T1, T2) -> mk_union([T1, T2]).

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


% if the name is the ID, transfer back the same way
erlang_ty_var_to_var({var, name, Name}) -> {var, Name};
erlang_ty_var_to_var({var, Id, Name}) ->
    {var, list_to_atom("$mu_" ++ integer_to_list(Id) ++ "_" ++ atom_to_list(Name))}.

erlang_ty_to_ast(X) ->
    Cache = erlang:get(ty_ast_cache),
    Cached = maps:get(X, Cache, undefined),
    FinalTy = maybe_transform(Cached, X, Cache),

    % SANITY CHECK
    % TODO is it always the case that once we are in the semantic world, when we go back we dont need the symtab?
    Sanity = ast_lib:ast_to_erlang_ty(FinalTy, symtab:empty()),
    % leave this sanity check for a while
    case ty_rec:is_equivalent(X, Sanity) of
    true -> ok;
    false ->
        % io:format(user, "--------~n", []),
        % io:format(user, "~p => ~p~n", [X, ty_ref:load(X)]),
        % io:format(user, "~p~n", [FinalTy]),
        raw_erlang_ty_to_ast(X), % check if this is really a pretty printing bug or a transformation bug
        error(pretty_printing_bug)
    end,

    FinalTy.

maybe_transform(undefined, X, Cache) ->
    V = erlang_ty_to_ast(X, #{}),
    CacheNew = maps:put(X, V, Cache),
    put(ty_ast_cache, CacheNew),
    V;
maybe_transform(V, _, _) ->
    V.

erlang_ty_to_ast(X, M) ->
        case M of
            #{X := Var} -> 
    % io:format(user,"Memoized ~p, replace with ~p~n", [X, Var]),
                Var;
            _ ->
        % Given a X = ... equation, create a new
        % TODO discuss how to ensure uniqueness
        RecVarID = erlang:unique_integer(),
        Var = {var, erlang:list_to_atom("$mu" ++ integer_to_list(RecVarID))},

        % io:format(user,"~n[~p]~nConverting~n~p := ~p with ~p~n", [R, Var, X, M]),
        NewM = M#{X => Var},

        {Pol, Full} = ty_rec:transform(
            X,
            #{
                to_fun => fun(S, T) -> stdtypes:tfun_full(lists:map(fun(F) ->
                    (erlang_ty_to_ast(F, NewM)) end,S),
                    (erlang_ty_to_ast(T, NewM))
                ) end,
                to_tuple => fun(Ts) -> stdtypes:ttuple(lists:map(fun(T) -> (erlang_ty_to_ast(T, NewM)) end,Ts)) end,
                to_atom => fun(A) -> stdtypes:tatom(A) end,
                to_list => fun(A, B) -> stdtypes:tlist_improper((erlang_ty_to_ast(A, NewM)), (erlang_ty_to_ast(B, NewM))) end,
                to_int => fun(S, T) -> stdtypes:trange(S, T) end,
                to_predef => fun('[]') -> stdtypes:tempty_list(); (Predef) -> {predef, Predef} end,
                to_map => fun(Assoc) -> stdtypes:tmap(Assoc) end,
                any_tuple => fun stdtypes:ttuple_any/0,
                any_tuple_i => fun(Size) -> stdtypes:ttuple([stdtypes:tany() || _ <- lists:seq(1, Size)]) end,
                any_function => fun stdtypes:tfun_any/0,
                any_function_i => fun(Size) -> stdtypes:tfun([stdtypes:tnone() || _ <- lists:seq(1, Size)], stdtypes:tany()) end,
                any_int => fun stdtypes:tint/0,
                any_list => fun stdtypes:tlist_any/0,
                any_atom => fun stdtypes:tatom/0,
                any_predef => fun stdtypes:tspecial_any/0,
                any_map => fun stdtypes:tmap_any/0,
                empty => fun stdtypes:tnone/0,
                any => fun stdtypes:tany/0,
                var => fun erlang_ty_var_to_var/1,
                diff => fun ast_lib:mk_diff/2,
                union => fun ast_lib:mk_union/1,
                intersect => fun ast_lib:mk_intersection/1,
                negate => fun ast_lib:mk_negation/1
            }),

        % io:format(user,"~n[~p]~nGot ~p~n", [R, {Pol, Full}]),
        % TODO check where to put the negation
        NewTy = case Pol of
            pos -> Full;
            neg -> stdtypes:tnegate(Full)
        end,
        % io:format(user,"~n[~p]~nNewTy ~p >> ~p~n", [R, X, NewTy]),

        % Return always recursive type
        % TODO check if Var in NewTy
        % if not, return just NewTy
        % io:format(user,"~n[~p]~nVar inside? ~p~n", [R, Var]),
        Vars = ast_utils:referenced_variables(NewTy),
        FinalTy = case lists:member(Var, Vars) of
            true ->
                {mu, Var, NewTy};
            false ->
                NewTy
        end,

        FinalTy
    end.

simplify(Full, Sym) ->
%%    io:format(user, ">> Full~n~p~n", [Full]),
    (_Dnf = {union, Unions}) = dnf:to_dnf(dnf:to_nnf(Full)),
%%    io:format(user, ">> DNF~n~p~n", [_Dnf]),
    % filter empty intersections
    FilterEmpty = {union, lists:filter(fun(E) -> not ty_rec:is_empty(ast_to_erlang_ty(E, Sym)) end, Unions)},

    % for any variable, extract them
    E = ast_to_erlang_ty(FilterEmpty, Sym),
    {Enew, Extracted} = extract_variables(E, ty_rec:all_variables(E), []),
    Neww = case Enew of
        E -> FilterEmpty;
        _ -> erlang_ty_to_ast(Enew, #{})
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

ast_to_erlang_ty(Ty) ->
    ast_to_erlang_ty(Ty, symtab:empty(), #{}).

ast_to_erlang_ty(Ty, Sym) ->
    ast_to_erlang_ty(Ty, Sym, #{}).

ast_to_erlang_ty({singleton, Atom}, _Sym, _) when is_atom(Atom) ->
    TyAtom = ty_atom:finite([Atom]),
    TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
    ty_rec:atom(TAtom);
ast_to_erlang_ty({singleton, IntOrChar}, _Sym, _) ->
    Int = dnf_var_int:int(ty_interval:interval(IntOrChar, IntOrChar)),
    ty_rec:interval(Int);
% TODO
ast_to_erlang_ty({binary, _, _}, _Sym, _) ->
    erlang:error("Bitstrings not implemented yet");

ast_to_erlang_ty({tuple_any}, _Sym, _) ->
    ty_rec:tuple();
ast_to_erlang_ty({tuple, Comps}, Sym, M) when is_list(Comps)->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T, Sym, M) end, Comps),

    T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
    ty_rec:tuple(length(Comps), T);

% funs
ast_to_erlang_ty({fun_simple}, _Sym, _) ->
    ty_rec:function();
ast_to_erlang_ty({fun_full, Comps, Result}, Sym, M) ->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T, Sym, M) end, Comps),
    TyB = ast_to_erlang_ty(Result, Sym, M),

    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, TyB))),
    ty_rec:function(length(Comps), T);

% maps
ast_to_erlang_ty({map_any}, _Sym, _M) ->
    ty_rec:map();
ast_to_erlang_ty({map, AssocList}, _Sym, _M) ->
    {_, TupPartTy, FunPartTy} = lists:foldl(
        fun({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
            case Association of
                map_field_opt ->
                    % tuples only
                    Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}),
                    {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), Functions};
                map_field_req ->
                    % tuples & functions
                    Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}),
                    Fun = ast_to_erlang_ty({fun_full, [mk_diff(Key, PrecedenceDomain)], Val}),
                    {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), ty_rec:intersect(Functions, Fun)}
            end
        end, {stdtypes:tnone(), ty_rec:empty(), ty_rec:function()}, AssocList),
    MapTuple = ty_tuple:tuple([TupPartTy, FunPartTy]),
    DnfMap = dnf_ty_map:map(MapTuple),
    VarDnfMap = dnf_var_ty_map:map(DnfMap),
    ty_rec:map(VarDnfMap);

% TODO records

% var
ast_to_erlang_ty(V = {var, A}, _Sym, M) ->
    % FIXME overloading of mu variables and normal variables
    case M of
        #{V := Ref} -> Ref;
        _ -> 
            % if this is a special $mu_integer()_name() variable, convert to that representation
            case string:prefix(atom_to_list(A), "$mu_") of 
                nomatch -> 
                    ty_rec:variable(ty_variable:new_with_name(A));
                IdName -> 
                    % assumption: erlang types generates variables only in this pattern: $mu_integer()_name()
                    [Id, Name] = string:split(IdName, "_"),
                    ty_rec:variable(ty_variable:new_with_name_and_id(list_to_integer(Id), list_to_atom(Name)))
            end
    end;

% ty_some_list
ast_to_erlang_ty({list, Ty}, Sym, M) -> ty_rec:union( ast_to_erlang_ty({improper_list, Ty, {empty_list}}, Sym, M), ast_to_erlang_ty({empty_list}, Sym, M) );
ast_to_erlang_ty({nonempty_list, Ty}, Sym, M) -> ast_to_erlang_ty({nonempty_improper_list, Ty, {empty_list}}, Sym, M);
ast_to_erlang_ty({nonempty_improper_list, Ty, Term}, Sym, M) -> ty_rec:diff(ast_to_erlang_ty({list, Ty}, Sym, M), ast_to_erlang_ty(Term, Sym, M));
ast_to_erlang_ty({improper_list, A, B}, Sym, M) ->
    ty_rec:list(dnf_var_ty_list:list(dnf_ty_list:list(ty_list:list(ast_to_erlang_ty(A, Sym, M), ast_to_erlang_ty(B, Sym, M)))));
ast_to_erlang_ty({empty_list}, _Sym, _) ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef('[]')));
ast_to_erlang_ty({predef, T}, _Sym, _) when T == pid; T == port; T == reference; T == float ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef(T)));

% named
ast_to_erlang_ty({named, Loc, Ref, Args}, Sym, M) ->
    case M of
        #{{Ref, Args} := NewRef} ->
            NewRef;
        _ ->
            ({ty_scheme, Vars, Ty}) = symtab:lookup_ty(Ref, Loc, Sym),

            % apply args to ty scheme
            Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
            NewTy = subst:apply(Map, Ty, no_clean),

            NewRef = ty_ref:new_ty_ref(),
            Res = ast_to_erlang_ty(NewTy, Sym, M#{{Ref, Args} => NewRef}),
            NewRes = ty_ref:define_ty_ref(NewRef, ty_ref:load(Res)),

            NewRes
    end;

% ty_predef_alias
ast_to_erlang_ty({predef_alias, Alias}, Sym, M) ->
    ast_to_erlang_ty(stdtypes:expand_predef_alias(Alias), Sym, M);

% ty_predef
ast_to_erlang_ty({predef, atom}, _, _) ->
    Atom = dnf_var_ty_atom:any(),
    ty_rec:atom(Atom);

ast_to_erlang_ty({predef, any}, _, _) -> ty_rec:any();
ast_to_erlang_ty({predef, none}, _, _) -> ty_rec:empty();
ast_to_erlang_ty({predef, integer}, _, _) ->
    ty_rec:interval();

% ints
ast_to_erlang_ty({range, From, To}, _, _) ->
    Int = dnf_var_int:int(ty_interval:interval(From, To)),
    ty_rec:interval(Int);

ast_to_erlang_ty({union, []}, _, _) -> ty_rec:empty();
ast_to_erlang_ty({union, [A]}, Sym, M) -> ast_to_erlang_ty(A, Sym, M);
ast_to_erlang_ty({union, [A|T]}, Sym, M) -> ty_rec:union(ast_to_erlang_ty(A, Sym, M), ast_to_erlang_ty({union, T}, Sym, M));

ast_to_erlang_ty({intersection, []}, _, _) -> ty_rec:any();
ast_to_erlang_ty({intersection, [A]}, Sym, M) -> ast_to_erlang_ty(A, Sym, M);
ast_to_erlang_ty({intersection, [A|T]}, Sym, M) -> ty_rec:intersect(ast_to_erlang_ty(A, Sym, M), ast_to_erlang_ty({intersection, T}, Sym, M));

ast_to_erlang_ty({negation, Ty}, Sym, M) -> ty_rec:negate(ast_to_erlang_ty(Ty, Sym, M));

ast_to_erlang_ty({mu, RecVar, Ty}, Sym, M) ->
    NewRef = ty_ref:new_ty_ref(),
    Mp = M#{RecVar => NewRef},
    InternalTy = ast_to_erlang_ty(Ty, Sym, Mp),
    _NewRes = ty_ref:define_ty_ref(NewRef, ty_ref:load(InternalTy));

ast_to_erlang_ty(T, _Sym, _M) ->
    erlang:error({"Norm not implemented or malformed type", T}).

-spec ast_to_erlang_ty_var(ast:ty_var()) -> ty_variable:var().
ast_to_erlang_ty_var({var, Name}) when is_atom(Name) ->
    ty_variable:new_with_name(Name).



% === useful for debugging
raw_erlang_ty_to_ast(X) ->
    FinalTy = raw_erlang_ty_to_ast(X, #{}),

    % SANITY CHECK
    % TODO is it always the case that once we are in the semantic world, when we go back we dont need the symtab?
    Sanity = ast_lib:ast_to_erlang_ty(FinalTy, symtab:empty()),
      % leave this sanity check for a while
      case ty_rec:is_equivalent(X, Sanity) of
        true -> ok;
        false ->
            % Dump = ty_ref:write_dump_ty(X),
            % io:format(user, "Dump~n~p~n", [Dump]),
            % io:format(user, "--------~n", []),
            % io:format(user, "~p => ~p~n", [X, ty_ref:load(X)]),
            % io:format(user, "~p~n", [FinalTy]),
            error(raw_printing_bug)
      end,
    
    FinalTy.



raw_erlang_ty_to_ast(X, M) ->
        case M of
            #{X := Var} -> Var;
            _ ->
        % Given a X = ... equation, create a new
        % TODO discuss how to ensure uniqueness
        RecVarID = erlang:unique_integer(),
        Var = {var, erlang:list_to_atom("$eq" ++ integer_to_list(RecVarID))},

        NewM = M#{X => Var},

        NewTy = 
        ty_rec:raw_transform(
            X,
            #{
                to_fun => fun(S, T) -> stdtypes:tfun_full(lists:map(fun(F) ->
                    (raw_erlang_ty_to_ast(F, NewM)) end,S),
                    (raw_erlang_ty_to_ast(T, NewM))
                ) end,
                to_tuple => fun(Ts) -> stdtypes:ttuple(lists:map(fun(T) -> (raw_erlang_ty_to_ast(T, NewM)) end,Ts)) end,
                to_atom => fun(A) -> stdtypes:tatom(A) end,
                to_list => fun(A, B) -> stdtypes:tlist_improper((raw_erlang_ty_to_ast(A, NewM)), (raw_erlang_ty_to_ast(B, NewM))) end,
                to_int => fun(S, T) -> stdtypes:trange(S, T) end,
                to_predef => fun('[]') -> stdtypes:tempty_list(); (Predef) -> {predef, Predef} end,
                to_map => fun(Assoc) -> stdtypes:tmap(Assoc) end,
                any_tuple => fun stdtypes:ttuple_any/0,
                any_tuple_i => fun(Size) -> stdtypes:ttuple([stdtypes:tany() || _ <- lists:seq(1, Size)]) end,
                any_function => fun stdtypes:tfun_any/0,
                any_function_i => fun(Size) -> stdtypes:tfun([stdtypes:tnone() || _ <- lists:seq(1, Size)], stdtypes:tany()) end,
                any_int => fun stdtypes:tint/0,
                any_list => fun stdtypes:tlist_any/0,
                any_atom => fun stdtypes:tatom/0,
                any_predef => fun stdtypes:tspecial_any/0,
                any_map => fun stdtypes:tmap_any/0,
                empty => fun stdtypes:tnone/0,
                any => fun stdtypes:tany/0,
                var => fun erlang_ty_var_to_var/1,
                diff => fun ast_lib:mk_diff/2,
                union => fun ast_lib:mk_union/1,
                intersect => fun ast_lib:mk_intersection/1,
                negate => fun ast_lib:mk_negation/1
            }),

        % Return always recursive type
        % if not, return just NewTy
        Vars = ast_utils:referenced_variables(NewTy),
        FinalTy = case lists:member(Var, Vars) of
            true ->
                {mu, Var, NewTy};
            false ->
                NewTy
        end,
        FinalTy
    end.