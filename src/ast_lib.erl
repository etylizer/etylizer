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
    maybe_transform(Cached, X, Cache).

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
              error(pretty_printing_bug)
          end,
        FinalTy
    end.


ast_to_erlang_ty(Ty, Sym) ->
    ErlangTy = ty_ref:new_ty_ref(),
    ok = convert(queue:from_list([{ErlangTy, Ty, _Memoization = #{}}]), Sym),
    ErlangTy.


convert(Queue, Sym) ->
    case queue:is_empty(Queue) of
        true -> ok;
        _ -> % convert next layer
            {{value, {ErlangTy, Ty, Memo}}, Q} = queue:out(Queue),
            {ErlangRec, NewQ} = do_convert(Ty, Q, Sym, Memo),
            % io:format(user, 
            %     "===~nFinished one layer~n~p :: ~p~nQueue:~n~p~n", 
            %     [ErlangTy, ErlangRec, NewQ]),
            ty_ref:define_ty_ref(ErlangTy, ErlangRec),
            convert(NewQ, Sym)
    end.

do_convert({singleton, Atom}, Q, _, _) when is_atom(Atom) ->
    TyAtom = ty_atom:finite([Atom]),
    TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
    {ty_rec:s_atom(TAtom), Q};
do_convert({singleton, IntOrChar}, Q, _, _) ->
    Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(IntOrChar, IntOrChar)),
    {ty_rec:s_interval(Int), Q};
% TODO
do_convert({binary, _, _}, _, _, _) ->
    erlang:error("Bitstrings not implemented yet");

do_convert({tuple_any}, Q, _, _) ->
    {ty_rec:s_tuple(), Q};
do_convert({tuple, Comps}, Q, Sym, M) when is_list(Comps)->
    {ETy, Q0} = lists:foldl(
        fun(Element, {Components, OldQ}) ->
            % to be converted later, add to queue
            Id = ty_ref:new_ty_ref(),
            {Components ++ [Id], queue:in({Id, Element, M}, OldQ)}
        end, {[], Q}, Comps),
    
    T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
    {ty_rec:s_tuple(length(Comps), T), Q0};

% funs
do_convert({fun_simple}, Q, _, _) ->
    {ty_rec:s_function(), Q};
do_convert({fun_full, Comps, Result}, Q, Sym, M) ->
    {ETy, Q0} = lists:foldl(
        fun(Element, {Components, OldQ}) ->
            % to be converted later, add to queue
            Id = ty_ref:new_ty_ref(),
            {Components ++ [Id], queue:in({Id, Element, M}, OldQ)}
        end, {[], Q}, Comps),
    {TyB, Q1} = do_convert(Result, Q0, Sym, M),
    
    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, TyB))),
    {ty_rec:s_function(length(Comps), T), Q1};

% maps
do_convert({map_any}, Q, _Sym, _M) ->
    {ty_rec:s_map(), Q};
do_convert({map, AssocList}, _Q, _Sym, _M) ->
    % TODO queue
    error(todo_convert_maps);
    % {_, TupPartTy, FunPartTy} = lists:foldl(
    %     fun({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
    %         case Association of
    %             map_field_opt ->
    %                 % tuples only
    %                 Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}, Sym),
    %                 {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), Functions};
    %             map_field_req ->
    %                 % tuples & functions
    %                 Tup = ast_to_erlang_ty({tuple, [mk_diff(Key, PrecedenceDomain), Val]}, Sym),
    %                 Fun = ast_to_erlang_ty({fun_full, [mk_diff(Key, PrecedenceDomain)], Val}, Sym),
    %                 {mk_union(PrecedenceDomain, Key), ty_rec:union(Tuples, Tup), ty_rec:intersect(Functions, Fun)}
    %         end
    %     end, {stdtypes:tnone(), ty_rec:empty(), ty_rec:function()}, AssocList),
    % MapTuple = ty_tuple:tuple([TupPartTy, FunPartTy]),
    % DnfMap = dnf_ty_map:map(MapTuple),
    % VarDnfMap = dnf_var_ty_map:map(DnfMap),
    % ty_rec:map(VarDnfMap);

% var
do_convert(V = {var, A}, Q, _Sym, M) ->
    % FIXME overloading of mu variables and normal variables
    case M of
        #{V := Ref} -> % mu variable
            % We are allowed to load the memoized ty_ref
            % because the second occurrence of the mu variable
            % is below a type constructor, 
            % i.e. the memoized reference is fully defined
            {ty_ref:load(Ref), Q};
        _ -> 
            % if this is a special $mu_integer()_name() variable, convert to that representation
            case string:prefix(atom_to_list(A), "$mu_") of 
                nomatch -> 
                    {ty_rec:s_variable(ty_variable:new_with_name(A)), Q};
                IdName -> 
                    % assumption: erlang types generates variables only in this pattern: $mu_integer()_name()
                    [Id, Name] = string:split(IdName, "_"),
                    {ty_rec:s_variable(ty_variable:new_with_name_and_id(list_to_integer(Id), list_to_atom(Name))), Q}
            end
    end;

% ty_some_list TODO List
% do_convert({list, Ty}, Q, Sym, _) -> 
%     ty_rec:union( ast_to_erlang_ty({improper_list, Ty, {empty_list}}, Sym, M), ast_to_erlang_ty({empty_list}, Sym, M) );
% ast_to_erlang_ty({nonempty_list, Ty}, Sym, M) -> ast_to_erlang_ty({nonempty_improper_list, Ty, {empty_list}}, Sym, M);
% ast_to_erlang_ty({nonempty_improper_list, Ty, Term}, Sym, M) -> ty_rec:diff(ast_to_erlang_ty({list, Ty}, Sym, M), ast_to_erlang_ty(Term, Sym, M));
do_convert({improper_list, A, B}, Q, _Sym, M) ->
    T1 = ty_ref:new_ty_ref(),
    T2 = ty_ref:new_ty_ref(),
    Q0 = queue:in({T1, A, M}, Q),
    Q1 = queue:in({T2, B, M}, Q0),
    
    {ty_rec:s_list(dnf_var_ty_list:list(dnf_ty_list:list(ty_list:list(
        T1,
        T2
    )))), Q1};
do_convert({empty_list}, Q, _Sym, _) ->
    {ty_rec:s_predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef('[]'))), Q};
do_convert({predef, T}, Q, _Sym, _M) when T == pid; T == port; T == reference; T == float ->
    {ty_rec:s_predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef(T))), Q};

% named
do_convert({named, Loc, Ref, Args}, _Q, Sym, M) ->
    error(todo_named);
    % case M of
    %     #{{Ref, Args} := NewRef} ->
    %         NewRef;
    %     _ ->
    %         ({ty_scheme, Vars, Ty}) = symtab:lookup_ty(Ref, Loc, Sym),

    %         % apply args to ty scheme
    %         Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
    %         NewTy = subst:apply(Map, Ty, no_clean),

    %         NewRef = ty_ref:new_ty_ref(),
    %         Res = ast_to_erlang_ty(NewTy, Sym, M#{{Ref, Args} => NewRef}),
    %         NewRes = ty_ref:define_ty_ref(NewRef, ty_ref:load(Res)),

    %         NewRes
    % end;

% ty_predef_alias
do_convert({predef_alias, Alias}, Q, Sym, M) ->
    do_convert(stdtypes:expand_predef_alias(Alias), Q, Sym, M);

% ty_predef
do_convert({predef, atom}, Q, _, _) ->
    Atom = dnf_var_ty_atom:any(),
    {ty_rec:s_atom(Atom), Q};

do_convert({predef, any}, Q, _, _) -> {ty_rec:s_any(), Q};
do_convert({predef, none}, Q, _, _) -> {ty_rec:s_empty(), Q};
do_convert({predef, integer}, Q, _, _) -> {ty_rec:s_interval(), Q};

% ints
do_convert({range, From, To}, Q, _, _) ->
    Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(From, To)),
    {ty_rec:s_interval(Int), Q};

do_convert({union, []}, Q, _, _) -> {ty_rec:s_empty(), Q};
do_convert({union, [A]}, Q, Sym, M) -> do_convert(A, Q, Sym, M);
do_convert({union, [A|T]}, Q, Sym, M) -> 
    {R1, Q1} = do_convert(A, Q, Sym, M),
    {R2, Q2} = do_convert({union, T}, Q1, Sym, M),
    {ty_rec:s_union(R1, R2), Q2};

do_convert({intersection, []}, Q, _, _) -> {ty_rec:s_any(), Q};
do_convert({intersection, [A]}, Q, Sym, M) -> do_convert(A, Q, Sym, M);
do_convert({intersection, [A|T]}, Q, Sym, M) -> 
    {R1, Q1} = do_convert(A, Q, Sym, M),
    {R2, Q2} = do_convert({intersection, T}, Q1, Sym, M),
    {ty_rec:s_intersect(R1, R2), Q2};

do_convert({negation, Ty}, Q, Sym, M) -> 
    {R, Q0} = do_convert(Ty, Q, Sym, M),
    {ty_rec:s_negate(R), Q0};

do_convert({mu, RecVar, Ty}, Q, Sym, M) ->
    NewRef = ty_ref:new_ty_ref(),
    Mp = M#{RecVar => NewRef},
    {InternalTy, NewQ} = do_convert(Ty, Q, Sym, Mp),
    % define recursive type
    ty_ref:define_ty_ref(NewRef, InternalTy),
    % return record
    {InternalTy, NewQ};

do_convert(T, _Q, _Sym, _M) ->
    erlang:error({"Transformation from ast:ty() to ty_rec:ty() not implemented or malformed type", T}).

-spec ast_to_erlang_ty_var(ast:ty_var()) -> ty_variable:var().
ast_to_erlang_ty_var({var, Name}) when is_atom(Name) ->
    ty_variable:new_with_name(Name).



% === useful for debugging
raw_erlang_ty_to_ast(X) ->
    raw_erlang_ty_to_ast(X, #{}).

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
            error(todo),
                {mu, Var, NewTy};
            false ->
                NewTy
        end,

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
        FinalTy
    end.