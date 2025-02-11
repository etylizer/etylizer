-module(ast_to_erlang_ty).

-ifdef(TEST).
-import(stdtypes, [tyscm/2, tmu/2, tvar/1, ttuple_any/0, tnegate/1, tatom/0, tatom/1, tfun_full/2, trange/2, tint/1, tunion/1, tintersect/1, trange_any/0, tint/0, ttuple/1, tany/0, tnone/0, tmap/1, tmap_any/0, tmap_field_req/2, tmap_field_opt/2]).
-import(test_utils, [extend_symtabs/2, extend_symtab/2, extend_symtab/3, is_subtype/2, is_equiv/2, named/1, named/2]).
-endif.

-export([ast_to_erlang_ty/2, reset/0]).

-include("sanity.hrl").

-type temporary_ref() :: 
    {local_ref, integer()} % fresh type references created for the queue
  | {mu_ref, atom()} 
  | {named_ref, {Ref :: term(), Args :: term()}}.

-spec new_local_ref() -> temporary_ref().
new_local_ref() -> {local_ref, erlang:unique_integer()}.

-spec var_ref(ast:ty_var()) -> temporary_ref().
var_ref(Var) -> {mu_ref, Var}.

-spec named_ref(ast:ty_ref(), [ast:ty()]) -> temporary_ref().
named_ref(Def, Args) -> {named_ref, {Def, Args}}.

-spec ast_to_erlang_ty(ast:ty(), symtab:t()) -> ty_rec:ty_ref().
ast_to_erlang_ty(Ty, Sym) ->
  % cache can't be shared across multiple ast_to_erlang_ty calls
  % we only have temporary references here
  reset(), 

  % 1. Convert to temporary local representation
  % Create a temporary type without internalizing the type refs
  % Instead use local type references stored in a local map
  LocalRef = new_local_ref(),
  Result = ?TIME(ast_parse_corec, convert(queue:from_list([{LocalRef, Ty, _Memoization = #{}}]), Sym, {#{}, #{}})),
  % io:format(user, "Result:~n~p~n", [{LocalRef, Result}]),
 
  % 2. Unify the results
  % TODO optimize unification, if needed at all
  % There can be many duplicate type references;
  % these will be substituted with their representative
  {UnifiedRef, UnifiedResult} = unify(LocalRef, Result),
  % {M1, _} = Result,
  % {UnifiedRef, UnifiedResult} = {LocalRef, M1},
  % io:format(user, "Unified Result:~n~p~n", [{UnifiedRef, UnifiedResult}]),

  % 3. create new type references and replace temporary ones
  %    return result reference
  ReplaceRefs = maps:from_list([{Ref, ty_ref:new_ty_ref()} || Ref <- maps:keys(UnifiedResult)]),
  {ReplacedRef, ReplacedResults} = replace_all({UnifiedRef, UnifiedResult}, ReplaceRefs),

  % 4. define types
  % [ty_ref:define_ty_ref(Ref, ToDefineTy) || Ref := ToDefineTy <- ReplacedResults],
  maps:map(fun(Ref, ToDefineTy) -> ty_ref:define_ty_ref(Ref, ToDefineTy) end, ReplacedResults),

  % free for garbage colletion
  reset(), 
  
  ReplacedRef.

replace_all({Ref, All}, Map) ->
  utils:everywhere(fun
    (RRef = {X, _}) when X == local_ref; X == mu_ref; X == named_ref -> 
      case Map of
        #{RRef := Replace} -> {ok, Replace};
        _ -> error
      end;
    (_) -> error
  end, {Ref, All}).
  

-type queue() :: queue:queue({temporary_ref(), ast:ty(), memo()}).
-type memo() :: #{}.
-type ty_rec() :: ty_rec:ty_rec().
% local database of type references; 
% ty_recs can share multiple references, these will be unified
-type result() :: {#{temporary_ref() => ty_rec()}, #{ty_rec() => [temporary_ref()]}}. 

reset() ->
  erlang:put(ast_ty_corec_cache, #{}),
  ok.

-spec group(#{A => list(X)}, A, X) -> #{A := list(X)}.
group(M, Key, Value) ->
  case M of
    #{Key := Group} -> M#{Key => lists:usort(Group ++ [Value])};
    _ -> M#{Key => [Value]}
  end.
-spec convert(queue(), symtab:t(), result()) -> result().
convert(Queue, Sym, Res) ->
  case queue:is_empty(Queue) of
    true -> 
      Res; 
    _ -> % convert next layer
      {{value, {LocalRef, Ty, Memo}}, Q} = queue:out(Queue),
      {ErlangRecOrLocalRef, NewQ, {R1, R2}} = maybe_do_convert({Ty, Res}, Q, Sym, Memo),
      convert(NewQ, Sym, {R1#{LocalRef => ErlangRecOrLocalRef}, group(R2, ErlangRecOrLocalRef, LocalRef)})
  end.

maybe_do_convert({Ty, Res}, Q, Sym, Memo) ->
  Cache = erlang:get(ast_ty_corec_cache),
  Cached = maps:get(Ty, Cache, undefined),
  maybe_do_convert_h(Cached, {Ty, Res}, Q, Sym, Memo, Cache).

maybe_do_convert_h(undefined, {X, Res}, Q, Sym, Memo, Cache) ->
  (Z = {Ty0, _Q0, _R0}) = do_convert({X, Res}, Q, Sym, Memo),
  CacheNew = maps:put(X, Ty0, Cache),
  put(ast_ty_corec_cache, CacheNew),
  Z;
maybe_do_convert_h(V, {_, Res}, Q, _, _, _) ->
  {V, Q, Res}.


-spec do_convert({ast:ty(), result()}, queue(), symtab:t(), memo()) -> {ty_rec(), queue(), result()}.
do_convert({{singleton, Atom}, R}, Q, _, _) when is_atom(Atom) ->
  TyAtom = ty_atom:finite([Atom]),
  TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
  {ty_rec:s_atom(TAtom), Q, R};
do_convert({{singleton, IntOrChar}, R}, Q, _, _) ->
  Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(IntOrChar, IntOrChar)),
  {ty_rec:s_interval(Int), Q, R};
do_convert({{bitstring}, R}, Q, _, _) ->
    {ty_rec:s_bitstring(), Q, R};
do_convert({{tuple_any}, R}, Q, _, _) ->
  {ty_rec:s_tuple(), Q, R};
do_convert({{tuple, Comps}, R}, Q, _Sym, M) when is_list(Comps)->
  {ETy, Q0} = lists:foldl(
    fun(Element, {Components, OldQ}) ->
      % to be converted later, add to queue
      Id = new_local_ref(),
      {Components ++ [Id], queue:in({Id, Element, M}, OldQ)}
    end, {[], Q}, Comps),
    
  T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
  {ty_rec:s_tuple(length(Comps), T), Q0, R};

% funs
do_convert({{fun_simple}, R}, Q, _, _) ->
    {ty_rec:s_function(), Q, R};
do_convert({{fun_full, Comps, Result}, R}, Q, _Sym, M) ->
    {ETy, Q0} = lists:foldl(
        fun(Element, {Components, OldQ}) ->
            % to be converted later, add to queue
            Id = new_local_ref(),
            {Components ++ [Id], queue:in({Id, Element, M}, OldQ)}
        end, {[], Q}, Comps),

    % add fun result to queue
    Id = new_local_ref(),
    Q1 = queue:in({Id, Result, M}, Q0),
    
    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, Id))),
    {ty_rec:s_function(length(Comps), T), Q1, R};
 
% maps 
do_convert({{map_any}, R}, Q, _Sym, _M) ->
    {ty_rec:s_map(), Q, R};
do_convert({{map, AssocList}, R}, Q, Sym, M) ->
    {_, TupPart, FunPart} = lists:foldl(
        fun({Association, Key, Val}, {PrecedenceDomain, Tuples, Functions}) ->
            case Association of
                map_field_opt ->
                    % tuples only
                    Tup = {tuple, [ast_lib:mk_diff(Key, PrecedenceDomain), Val]},
                    {ast_lib:mk_union([PrecedenceDomain, Key]), ast_lib:mk_union([Tuples, Tup]), Functions};
                map_field_req ->
                    % tuples & functions
                    Tup = {tuple, [ast_lib:mk_diff(Key, PrecedenceDomain), Val]},
                    Fun = {fun_full, [ast_lib:mk_diff(Key, PrecedenceDomain)], Val},
                    {ast_lib:mk_union([PrecedenceDomain, Key]), ast_lib:mk_union([Tuples, Tup]), ast_lib:mk_intersection([Functions, Fun])}
            end
        end, {stdtypes:tnone(), stdtypes:tnone(), stdtypes:tfun_any()}, AssocList),
    MapTuple = stdtypes:ttuple([TupPart, FunPart]),
    % TODO: the tuple introduced here (Recc) can be cleaned up in the final temp_ref -> rec mapping
    {Recc, Q0, R0} = do_convert({MapTuple, R}, Q, Sym, M),
    {ty_rec:tuple_to_map(Recc), Q0, R0};

% var
do_convert({V = {var, A}, R = {IdTy, _}}, Q, _Sym, M) ->
  % FIXME overloading of mu variables and normal variables
  case M of
    #{V := Ref} -> % mu variable
      % io:format(user,"R: ~p~n", [{Ref, R}]),
      #{Ref := Ty} = IdTy,
      % We are allowed to load the memoized ref
      % because the second occurrence of the mu variable
      % is below a type constructor, 
      % i.e. the memoized reference is fully (partially) defined
      {Ty, Q, R};
    _ -> 
      % if this is a special $mu_integer()_name() variable, convert to that representation
      case string:prefix(atom_to_list(A), "$mu_") of 
        nomatch -> 
          {ty_rec:s_variable(ty_variable:new_with_name(A)), Q, R};
        IdName -> 
          % assumption: erlang types generates variables only in this pattern: $mu_integer()_name()
          [Id, Name] = string:split(IdName, "_"),
          {ty_rec:s_variable(ty_variable:new_with_name_and_id(list_to_integer(Id), list_to_atom(Name))), Q, R}
      end
  end;

do_convert({{list, Ty}, R}, Q, Sym, M) ->
  do_convert({stdtypes:tunion([
    {improper_list, Ty, {empty_list}}, 
    {empty_list}
  ]), R}, Q, Sym, M);
do_convert({{nonempty_list, Ty}, R}, Q, Sym, M) ->
  do_convert({{nonempty_improper_list, Ty, {empty_list}}, R}, Q, Sym, M);
do_convert({{nonempty_improper_list, Ty, Term}, R}, Q, Sym, M) ->
  do_convert({stdtypes:tintersect([{list, Ty}, stdtypes:tnegate(Term)]), R}, Q, Sym, M);
do_convert({{improper_list, A, B}, R}, Q, _Sym, M) ->
    T1 = new_local_ref(),
    T2 = new_local_ref(),
    Q0 = queue:in({T1, A, M}, Q),
    Q1 = queue:in({T2, B, M}, Q0),
    
    {ty_rec:s_list(dnf_var_ty_list:list(dnf_ty_list:list(ty_list:list( T1, T2)))), Q1, R};
do_convert({{empty_list}, R}, Q, _Sym, _) ->
    {ty_rec:s_predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef('[]'))), Q, R};
do_convert({{predef, T}, R}, Q, _Sym, _M) when T == pid; T == port; T == reference; T == float ->
    {ty_rec:s_predef(dnf_var_ty_predef:predef(dnf_ty_predef:predef(T))), Q, R};

% named
do_convert({{named, Loc, Ref, Args}, R = {IdTy, _}}, Q, Sym, M) ->
  case M of
    #{{Ref, Args} := NewRef} ->
      #{NewRef := Ty} = IdTy,
      {Ty, Q, R};
    _ ->
      ({ty_scheme, Vars, Ty}) = symtab:lookup_ty(Ref, Loc, Sym),

      % apply args to ty scheme
      Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
      NewTy = subst:apply(Map, Ty, no_clean),
      
      % create a new reference (ref args pair) and memoize
      NewRef = named_ref(Ref, Args),
      Mp = M#{{Ref, Args} => NewRef},
      {InternalTy, NewQ, {R0, R1}} = maybe_do_convert({NewTy, R}, Q, Sym, Mp),
      
      {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}}
  end;

% % ty_predef_alias
do_convert({{predef_alias, Alias}, R}, Q, Sym, M) ->
    do_convert({stdtypes:expand_predef_alias(Alias), R}, Q, Sym, M);

% % ty_predef
do_convert({{predef, atom}, R}, Q, _, _) ->
    Atom = dnf_var_ty_atom:any(),
    {ty_rec:s_atom(Atom), Q, R};

do_convert({{predef, any}, R}, Q, _, _) -> {ty_rec:s_any(), Q, R};
do_convert({{predef, none}, R}, Q, _, _) -> {ty_rec:s_empty(), Q, R};
do_convert({{predef, integer}, R}, Q, _, _) -> {ty_rec:s_interval(), Q, R};
 
% ints
do_convert({{range, From, To}, R}, Q, _, _) ->
    Int = dnf_var_ty_interval:int(dnf_ty_interval:interval(From, To)),
    {ty_rec:s_interval(Int), Q, R};

do_convert({{union, []}, R}, Q, _, _) -> {ty_rec:s_empty(), Q, R};
do_convert({{union, [A]}, R}, Q, Sym, M) -> do_convert({A, R}, Q, Sym, M);
do_convert({{union, [A|T]}, R}, Q, Sym, M) -> 
  {R1, Q1, RR1} = do_convert({A, R}, Q, Sym, M),
  {R2, Q2, RR2} = do_convert({{union, T}, RR1}, Q1, Sym, M),
  {ty_rec:s_union(R1, R2), Q2, RR2};

do_convert({{intersection, []}, R}, Q, _, _) -> {ty_rec:s_any(), Q, R};
do_convert({{intersection, [A]}, R}, Q, Sym, M) -> do_convert({A, R}, Q, Sym, M);
do_convert({{intersection, [A|T]}, R}, Q, Sym, M) -> 
  {R1, Q1, RR0} = do_convert({A, R}, Q, Sym, M),
  {R2, Q2, RR1} = do_convert({{intersection, T}, RR0}, Q1, Sym, M),
  {ty_rec:s_intersect(R1, R2), Q2, RR1};

do_convert({{negation, Ty}, R}, Q, Sym, M) -> 
  {NewR, Q0, RR0} = do_convert({Ty, R}, Q, Sym, M),
  {ty_rec:s_negate(NewR), Q0, RR0};

do_convert({{mu, RecVar, Ty}, R}, Q, Sym, M) ->
  NewRef = var_ref(RecVar),
  Mp = M#{RecVar => NewRef},
  {InternalTy, NewQ, {R0, R1}} = do_convert({Ty, R}, Q, Sym, Mp),
  % return record
  {InternalTy, NewQ, {R0#{NewRef => InternalTy}, group(R1, InternalTy, NewRef)}};

do_convert(T, _Q, _Sym, _M) ->
  erlang:error({"Transformation from ast:ty() to ty_rec:ty() not implemented or malformed type", T}).


-spec unify(temporary_ref(), result()) -> {temporary_ref(), #{temporary_ref() => ty_rec()}}.
unify(Ref, {IdToTy, TyToIds}) ->
  % map with references to unify, pick representatives
  %ToUnify = maps:to_list(#{K => choose_representative(V) || K := V <- TyToIds, length(V) > 1}), 
  ToUnify = maps:to_list(maps:filtermap(fun(_K, V) when length(V) =< 1 -> false;(_K, V) -> {true, choose_representative(V)} end, TyToIds)),
  % replace equivalent refs with representative
  {UnifiedRef, {UnifiedIdToTy, _UnifiedTyToIds}} = unify(Ref, {IdToTy, TyToIds}, ToUnify),
  {UnifiedRef, UnifiedIdToTy}.

-spec choose_representative([temporary_ref()]) -> {temporary_ref(), [temporary_ref()]}.
choose_representative(Refs) ->
  [Representative | Others] = lists:usort(
    fun
      ({Other, _}, {named_ref, _}) when Other == local_ref; Other == mu_ref -> false;
      ({local_ref, _}, {mu_ref, _}) -> false;
      ({_, X}, {_, Y}) -> X =< Y
    end, 
    Refs),
  {Representative, Others}.

% -spec unify(temporary_ref(), result(), Worklist) -> 
%   {temporary_ref(), result(), Worklist} 
%   when Worklist :: [{ty_rec(), {temporary_ref(), [temporary_ref()]}}].
% TODO utils:everywhere too slow, more efficient unify
unify(Ref, {IdToTy, TyToIds}, [{_Ty, {Representative, Duplicates}} | Xs])->
  {NewRef, {NewIdToTy, NewTyToIds}} =
  utils:everywhere(fun
    (RRef = {X, _}) when X == local_ref; X == mu_ref; X == named_ref -> 
      case lists:member(RRef, Duplicates) of
        true -> {ok, Representative};
        false -> error
      end;
    (_) -> error
  end, {Ref, {IdToTy, TyToIds}}),
  unify(NewRef, {NewIdToTy, NewTyToIds}, Xs);
unify(Ref, Db, [])->
  {Ref, Db}.


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% parse(AstType) ->
%   parse(AstType, symtab:empty()).

% parse(AstType, Symtab) ->
%   ast_to_erlang_ty(AstType, Symtab).

parse_test() ->
  test_utils:reset_ets(),

  % Ty1 = parse(tatom(a)),
  % Ty2 = parse(ttuple([tatom(a)])),
  % Ty3 = parse(ttuple([tatom(a), tatom(a), tatom(a)])),
  % Ty4 = parse(tmu(tvar(x), ttuple([tvar(x), tvar(x)]))),
  
  % St5 = test_utils:extend_symtab(exp, tyscm([], ttuple([named(exp), named(exp)]))),
  % Ty5 = parse(named(exp), St5),
 
  % mutual recursion
  % St6 = 
  %   extend_symtabs(
  %       [
  %           {exp, tyscm([], tunion([ttuple([tatom(a)]), ttuple([named(exp2), named(exp2)])]))},
  %           {exp2, tyscm([], ttuple([named(exp), named(exp)]))}
  %       ],
  %       symtab:empty()
  %   ),
  % Ty6 = parse(named(exp), St6),
  
  % St7 = test_utils:extend_symtab(exp, tyscm([], tunion([
  %   tatom(b), 
  %   ttuple([tatom(a), named(exp)])
  % ]))),
  % Ty7 = parse(named(exp), St7),
  
  % St8 = test_utils:extend_symtab(exp, tyscm([], tatom(a) )),
  % Ty8 = parse(ttuple([named(exp), tmu(tvar(x), tatom(a))]), St8),
  
  % parameterized type
  % St9 = test_utils:extend_symtab(exp, tyscm([a], tunion([
  %   tatom(a), 
  %   ttuple([tvar(a), named(exp, [tatom(b)])])
  % ]))),
  % Ty9 = parse(named(exp, [tatom(b)]), St9),
  
  % St10 = test_utils:extend_symtab(t, tyscm([k, v], tmap([ tmap_field_opt(tvar(k), tvar(v)) ]))),
  % Ty10 = parse(named(t, [tvar(k), tvar(v)]), St10),


  ok.

-endif.