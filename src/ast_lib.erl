-module(ast_lib).

-export([
    reset/0,
    ast_to_erlang_ty/2,
    erlang_ty_to_ast/1, erlang_ty_to_ast/2,
    ast_to_erlang_ty_var/1,
    mk_union/1,
    mk_negation/1,
    mk_diff/2,
    mk_intersection/1
]).

-ifdef(TEST).
-export([
    erlang_ty_var_to_var/1
   ]).
-endif.


reset() ->
    erlang:put(ty_ast_cache, #{}),
    erlang:put(ast_ty_cache, #{}),
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
                            [] -> errors:bug(utils:sformat("~w", Tys));
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
        %   io:format(user, "--------~n", []),
        %   io:format(user, "~p => ~p~n", [X, ty_ref:load(X)]),
        %   io:format(user, "~p~n", [FinalTy]),
          raw_erlang_ty_to_ast(X), % check if this is really a pretty printing bug or a transformation bug
          errors:bug("Pretty printing bug")
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
            #{X := Var} -> Var;
            _ ->
        % Given a X = ... equation, create a new
        % TODO discuss how to ensure uniqueness
        RecVarID = erlang:unique_integer(),
        Var = {var, erlang:list_to_atom("$mu" ++ integer_to_list(RecVarID))},

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
                any_bitstring => fun stdtypes:tbitstring/0,
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

        % TODO check where to put the negation
        NewTy = case Pol of
            pos -> Full;
            neg -> stdtypes:tnegate(Full)
        end,

        % Return always recursive type
        % TODO check if Var in NewTy
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

replace_loc(Ty) ->
  utils:everywhere(fun
    ({loc, _, _, _}) -> {ok, ast:loc_auto()};
    (_) -> error
  end, Ty).

ast_to_erlang_ty(TyLoc, Symtab) ->
  % remove loc annotations for better caching behavior
  Ty = replace_loc(TyLoc),
  Cache = erlang:get(ast_ty_cache),
  Cached = maps:get(Ty, Cache, undefined),
  maybe_parse(Cached, Ty, Cache, Symtab).

maybe_parse(undefined, X, Cache, Symtab) ->
    V = parse_ast_to_erlang_ty(X, Symtab),
    CacheNew = maps:put(X, V, Cache),
    put(ast_ty_cache, CacheNew),
    V;
maybe_parse(V, _, _, _) ->
    V.


parse_ast_to_erlang_ty({singleton, Atom}, _Sym) when is_atom(Atom) ->
    TyAtom = ty_atom:finite([Atom]),
    TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
    ty_rec:atom(TAtom);
parse_ast_to_erlang_ty({singleton, IntOrChar}, _Sym) ->
    Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(IntOrChar, IntOrChar)),
    ty_rec:interval(Int);
parse_ast_to_erlang_ty({bitstring}, _Sym) ->
    ty_rec:bitstring();
parse_ast_to_erlang_ty({tuple_any}, _Sym) ->
    ty_rec:tuple();
parse_ast_to_erlang_ty({tuple, Comps}, Sym) when is_list(Comps)->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T, Sym) end, Comps),

    T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
    ty_rec:tuple(length(Comps), T);

% funs
parse_ast_to_erlang_ty({fun_simple}, _Sym) ->
    ty_rec:function();
parse_ast_to_erlang_ty({fun_full, Comps, Result}, Sym) ->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T, Sym) end, Comps),
    TyB = ast_to_erlang_ty(Result, Sym),

    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, TyB))),
    ty_rec:function(length(Comps), T);

% maps
parse_ast_to_erlang_ty({map_any}, _Sym) ->
    ty_rec:map();
parse_ast_to_erlang_ty({map, AssocList}, Sym) ->
    {_, TupPartTy, FunPartTy} = lists:foldl(
        fun({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
            case Association of
                map_field_opt ->
                    % tuples only
                    Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}, Sym),
                    {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), Functions};
                map_field_req ->
                    % tuples & functions
                    Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}, Sym),
                    Fun = ast_to_erlang_ty({fun_full, [mk_diff(Key, PrecedenceDomain)], Val}, Sym),
                    {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), ty_rec:intersect(Functions, Fun)}
            end
        end, {stdtypes:tnone(), ty_rec:empty(), ty_rec:function()}, AssocList),
    MapTuple = ty_tuple:tuple([TupPartTy, FunPartTy]),
    DnfMap = dnf_ty_map:map(MapTuple),
    VarDnfMap = dnf_var_ty_map:map(DnfMap),
    ty_rec:map(VarDnfMap);

% TODO records

% var
parse_ast_to_erlang_ty({var, A}, _Sym) ->
    % if this is a special $mu_integer()_name() variable, convert to that representation
    case string:prefix(atom_to_list(A), "$mu_") of
        nomatch ->
            ty_rec:variable(ty_variable:new_with_name(A));
        IdName ->
            % assumption: erlang types generates variables only in this pattern: $mu_integer()_name()
            [Id, Name] = string:split(IdName, "_"),
            ty_rec:variable(ty_variable:new_with_name_and_id(list_to_integer(Id), list_to_atom(Name)))
    end;

% ty_some_list
parse_ast_to_erlang_ty({list, Ty}, Sym) -> ty_rec:union( ast_to_erlang_ty({improper_list, Ty, {empty_list}}, Sym), ast_to_erlang_ty({empty_list}, Sym) );
parse_ast_to_erlang_ty({nonempty_list, Ty}, Sym) -> ast_to_erlang_ty({nonempty_improper_list, Ty, {empty_list}}, Sym);
parse_ast_to_erlang_ty({nonempty_improper_list, Ty, Term}, Sym) -> ty_rec:diff(ast_to_erlang_ty({list, Ty}, Sym), ast_to_erlang_ty(Term, Sym));
parse_ast_to_erlang_ty({improper_list, A, B}, Sym) ->
    ty_rec:list(dnf_var_ty_list:list(dnf_ty_list:list(ty_list:list(ast_to_erlang_ty(A, Sym), ast_to_erlang_ty(B, Sym)))));
parse_ast_to_erlang_ty({empty_list}, _Sym) ->
    ty_rec:predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef('[]')));
parse_ast_to_erlang_ty({predef, T}, _Sym) when T == pid; T == port; T == reference; T == float ->
    ty_rec:predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef(T)));

% named
parse_ast_to_erlang_ty(Ty = {named, _Loc, _Ref, _Args}, Sym) ->
    % todo check if really recursive
    ast_to_erlang_ty:ast_to_erlang_ty(Ty, Sym);

% ty_predef_alias
parse_ast_to_erlang_ty({predef_alias, Alias}, Sym) ->
    ast_to_erlang_ty(stdtypes:expand_predef_alias(Alias), Sym);

% ty_predef
parse_ast_to_erlang_ty({predef, atom}, _) ->
    Atom = dnf_var_ty_atom:any(),
    ty_rec:atom(Atom);

parse_ast_to_erlang_ty({predef, any}, _) -> ty_rec:any();
parse_ast_to_erlang_ty({predef, none}, _) -> ty_rec:empty();
parse_ast_to_erlang_ty({predef, integer}, _) ->
    ty_rec:interval();

% ints
parse_ast_to_erlang_ty({range, From, To}, _) ->
    Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(From, To)),
    ty_rec:interval(Int);

parse_ast_to_erlang_ty({union, []}, _) -> ty_rec:empty();
parse_ast_to_erlang_ty({union, [A]}, Sym) -> ast_to_erlang_ty(A, Sym);
parse_ast_to_erlang_ty({union, [A|T]}, Sym) -> ty_rec:union(ast_to_erlang_ty(A, Sym), ast_to_erlang_ty({union, T}, Sym));

parse_ast_to_erlang_ty({intersection, []}, _) -> ty_rec:any();
parse_ast_to_erlang_ty({intersection, [A]}, Sym) -> ast_to_erlang_ty(A, Sym);
parse_ast_to_erlang_ty({intersection, [A|T]}, Sym) -> ty_rec:intersect(ast_to_erlang_ty(A, Sym), ast_to_erlang_ty({intersection, T}, Sym));

parse_ast_to_erlang_ty({negation, Ty}, Sym) -> ty_rec:negate(ast_to_erlang_ty(Ty, Sym));

parse_ast_to_erlang_ty(Ty = {mu, Var, InnerTy}, Sym) ->
    % TODO test case if this is capture-avoiding
    % what happens with mu X . mu X . X,
    % assumme type is well-formed and this case should not happen?
    Vars = ast_utils:referenced_variables(InnerTy),
    case lists:member(Var, Vars) of
        true ->
            % assumption: Var is inside InnerTy
            ast_to_erlang_ty:ast_to_erlang_ty(Ty, Sym);
        false ->
            % TODO assume this is simplified before and well-formed ast includes mu -> recursive?
            % otherwise: simplify, not a recursive type
            ast_to_erlang_ty(InnerTy, Sym)
    end;

parse_ast_to_erlang_ty(T, _Sym) ->
    errors:bug({"Norm not implemented or malformed type", T}).


-spec ast_to_erlang_ty_var(ast:ty_var()) -> ty_variable:var().
ast_to_erlang_ty_var({var, Name}) when is_atom(Name) ->
    ty_variable:new_with_name(Name).

% === useful for debugging
raw_erlang_ty_to_ast(X) ->
    FinalTy = raw_erlang_ty_to_ast(X, #{}),
    
    % SANITY CHECK
    % TODO is it always the case that once we are in the semantic world, when we go back we dont need the symtab?
    Sanity = parse_ast_to_erlang_ty(FinalTy, symtab:empty()),
      % leave this sanity check for a while
      case ty_rec:is_equivalent(X, Sanity) of
        true -> ok;
        false ->
            % Dump = ty_ref:write_dump_ty(X),
            % io:format(user, "Dump~n~p~n", [Dump]),
            % io:format(user, "--------~n", []),
            % io:format(user, "~p => ~p~n", [X, ty_ref:load(X)]),
            % io:format(user, "~p~n", [FinalTy]),
            errors:bug("Raw printing bug")
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
                any_bitstring => fun stdtypes:tbitstring/0,
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
