-module(ty_rec).

-export([union/2, intersect/2, diff/2, negate/1, empty/0, any/0]).
-export([norm/1, eval/1, pi/2]).

-export([substitute_bdd/2]).

-export([is_empty/3]).

-import(stdtypes, [tvar/1]).

-record(ty, {atoms,ints,special,list,prod,arrw}).

rep_map_any()  -> {bdd_lazy:any(), #{}}.
rep_map_none() -> {bdd_lazy:empty(), #{}}.

empty() -> #ty{atoms = bdd_lazy:empty(), ints = bdd_lazy:empty(), special = bdd_lazy:empty(), list = bdd_lazy:empty(), prod = rep_map_none(), arrw = rep_map_none()}.
any() ->   #ty{atoms = bdd_lazy:any(), ints = bdd_lazy:any(), special = bdd_lazy:any(), list = bdd_lazy:any(), prod = rep_map_any(), arrw = rep_map_any()}.


% ==================
% ast:ty() -> BDD  |
% ==================
%
% Conversion of a type into a BDD representation
% Puts the parsed type into an empty BDD
%
% Conversion is complete, i.e. it recursively parses all inside nodes of
% tuples and functions
%
%
% Type variables are represented as
% the variable intersected with each disjunct unions top-type
%
% named references are saved in each partition as well and are unfolded on demand
% ===============================

% ty_singleton
norm({singleton, Atom}) when is_atom(Atom) ->
  (empty())#ty{atoms = bdd_lazy:pos({bdd_atom, Atom})};
norm({singleton, IntOrChar}) ->
  % Char is subset of Int
  (empty())#ty{ints = bdd_lazy:pos({bdd_range, IntOrChar, IntOrChar})};

% ty_bitstring % TODO
norm({binary, _, _}) -> erlang:error("Bitstrings not supported yet");

norm({tuple_any}) -> (empty())#ty{prod = rep_map_any()};
norm({tuple, Components}) ->
  Normed = [norm(Ty) || Ty <- Components],
  Tuple = #{length(Components) => bdd_lazy:pos({bdd_tuple, Normed})},
  (empty())#ty{prod = {bdd_lazy:empty(), Tuple}};

% funs
norm({fun_simple}) ->
  (empty())#ty{arrw = {bdd_lazy:any(), #{}}};
norm({fun_full, Components, Result}) ->
  Normed = [norm(Ty) || Ty <- Components],
  Function = #{length(Components) => bdd_lazy:pos({bdd_fun_full, Normed, norm(Result)})},
  (empty())#ty{arrw = {bdd_lazy:empty(), Function}};


% var
norm({var, A}) ->
  V = {bdd_var, A},
  (any())#ty{
    atoms = bdd_lazy:pos(V),
    ints = bdd_lazy:pos(V),
    special = bdd_lazy:pos(V),
    list = bdd_lazy:pos(V),
    prod = {bdd_lazy:pos(V), #{}},
    arrw = {bdd_lazy:pos(V), #{}}
  };

% ty_some_list
norm({list, Ty}) ->
  union(
    norm({improper_list, Ty, {empty_list}}),
    norm({empty_list})
  );
norm({nonempty_list, Ty}) -> norm({nonempty_improper_list, Ty, {empty_list}});
norm({nonempty_improper_list, Ty, Term}) -> diff(norm({list, Ty}), norm(Term));
norm({improper_list, Ty, Term}) ->
  (empty())#ty{ list = bdd_lazy:pos({bdd_list, norm(Ty), norm(Term)}) };

norm({empty_list}) ->
  (empty())#ty{special = bdd_lazy:pos({bdd_spec, empty_list})};
norm({predef, T}) when T == pid; T == port; T == reference; T == float ->
  (empty())#ty{special = bdd_lazy:pos({bdd_spec, T})};

% named
norm({named, _, Ref, Args}) ->
  V = {bdd_named, {Ref, Args}},
  (any())#ty{
    atoms = bdd_lazy:pos(V),
    ints = bdd_lazy:pos(V),
    special = bdd_lazy:pos(V),
    list = bdd_lazy:pos(V),
    prod = {bdd_lazy:pos(V), #{}},
    arrw = {bdd_lazy:pos(V), #{}}
  };

% ty_predef_alias
norm({predef_alias, Alias}) ->
  Expanded = stdtypes:expand_predef_alias(Alias),
  norm(Expanded);

% ty_predef
norm({predef, atom}) ->
  (empty())#ty{atoms = bdd_lazy:any()};

norm({predef, any}) -> any();
norm({predef, none}) -> empty();
norm({predef, integer}) ->
  (empty())#ty{ints = bdd_lazy:pos({bdd_range, '*', '*'})};

% ints
norm({range, From, To}) ->
  (empty())#ty{ints = bdd_lazy:pos({bdd_range, From, To})};

norm({union, []}) -> empty();
norm({union, [A]}) -> norm(A);
norm({union, [A|T]}) -> union(norm(A), norm({union, T}));

norm({intersection, []}) -> any();
norm({intersection, [A]}) -> norm(A);
norm({intersection, [A|T]}) -> intersect(norm(A), norm({intersection, T}));

norm({negation, Ty}) -> negate(norm(Ty));

norm(T) ->
  logger:error("Norm not implemented for~n~p", [T]),
  erlang:error("Norm not implemented, see error log").

% ==================
% BDD -> ast:ty()  |
% ==================
%
% A BDD is a disjunct union of all its partitions:
%
% Atoms
% Special types: pid, port, reference, float, empty_list
% Lists: proper (List A), improper (List A Termination)
%        a proper list is a improper list with a special termination symbol with additional [] symbol
%        List A =:= Improper A []  U  []
% Maps TODO
% Records TODO
% Infinite union over every n-tuple for n ∈ ℕ
%   represented as having a default mapping for all n ∈ ℕ
%   all tuples which differ from the default value are tracked explicitly
% Infinite union over every n-function for n ∈ ℕ
%   same representation as n-tuple
% ===============================

eval(#ty{atoms = At, ints = I, special = S, list = L, prod = {DefP, P}, arrw = {DefA, A}}) ->
  {union, [
    {intersection, [{predef, atom}, bdd_lazy:eval(At)]},
    {intersection, [{predef, integer}, bdd_lazy:eval(I)]},
    {intersection, [stdtypes:tspecial_any(), bdd_lazy:eval(S)]},
    {intersection, [stdtypes:tlist_any(), bdd_lazy:eval(L)]},
    {union, eval_inf_union(DefP, P, fun stdtypes:ttuple_n/1, {tuple_any})},
    {union, eval_inf_union(DefA, A, fun stdtypes:tarrow_n/1, {fun_simple})}
  ]}.

eval_inf_union({bdd, 0}, Explicit, AnyNGenerator, _) ->
  Eval = fun({Length, Tuple}) ->
    {intersection, [AnyNGenerator(Length), bdd_lazy:eval(Tuple)]}
         end,
  lists:map(Eval, maps:to_list(Explicit));
eval_inf_union(Default, A, AnyNGenerator, TopType) ->
  Others = {union, eval_inf_union({bdd, 0}, A, AnyNGenerator, TopType)},
  % others union with ((any -> T) function WITHOUT any (n -> T)-functions which are already captured by Others)
  OtherNAny = [{negation, AnyNGenerator(N)} || N <- maps:keys(A)],
  [Others, {intersection, [TopType] ++ OtherNAny ++ [bdd_lazy:eval(Default)]}].

% ==================
% BDD set-theoretic operations
% union
% intersection
% difference
% negation
% ==================

union(#ty{atoms = T1, ints = I1, special = S1, list = L1, prod = P1, arrw = A1},
      #ty{atoms = T2, ints = I2, special = S2, list = L2, prod = P2, arrw = A2}
      ) ->
        #ty{atoms = bdd_lazy:union(T1, T2),
          special = bdd_lazy:union(S1, S2),
          ints = bdd_lazy:union(I1, I2),
          list = bdd_lazy:union(L1, L2),
          prod = multi_union(P1, P2),
          arrw = multi_union(A1, A2)}.

intersect(
    #ty{atoms = T1, ints = I1, special = S1, list = L1, prod = P1, arrw = A1},
    #ty{atoms = T2, ints = I2, special = S2, list = L2, prod = P2, arrw = A2}
) ->
        #ty{atoms = bdd_lazy:intersect(T1, T2),
          ints = bdd_lazy:intersect(I1, I2),
          special =  bdd_lazy:intersect(S1, S2),
          list = bdd_lazy:intersect(L1, L2),
          prod = multi_intersect(P1, P2),
          arrw = multi_intersect(A1, A2)}.

diff(#ty{atoms = T1, ints = I1, special = S1, list = L1, prod = P1, arrw = A1},
      #ty{atoms = T2, ints = I2, special = S2, list = L2, prod = P2, arrw = A2}
      ) ->
        #ty{atoms = bdd_lazy:diff(T1, T2),
          special = bdd_lazy:diff(S1, S2),
          ints = bdd_lazy:diff(I1, I2),
          list = bdd_lazy:diff(L1, L2),
        prod = multi_diff(P1, P2),
        arrw = multi_diff(A1, A2)}.

negate(B) ->
  diff(any(), B).

multi_union({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    bdd_lazy:union(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
                 end,
  {bdd_lazy:union(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

multi_intersect({DefaultT1, T1}, {DefaultT2, T2}) ->
  % get all keys
  AllKeys = maps:keys(T1) ++ maps:keys(T2),
  IntersectKey = fun(Key) ->
    bdd_lazy:intersect(
      maps:get(Key, T1, DefaultT1),
      maps:get(Key, T2, DefaultT2)
    )
    end,
  {bdd_lazy:intersect(DefaultT1, DefaultT2), maps:from_list([{Key, IntersectKey(Key)} || Key <- AllKeys])}.

multi_diff({DefaultT1, T1}, {DefaultT2, T2}) ->
  % all on left side
  M1 = maps:map(fun(Length, BddT1) ->
    Other = maps:get(Length, T2, DefaultT2),
    bdd_lazy:diff(BddT1, Other)
           end, T1),

  % rest on right side that are not in left side
  M2_orig = maps:filter(fun(Length, _) -> not maps:is_key(Length, M1) end, T2),
  M2 = maps:map(fun(_Length, Bdd) ->
    bdd_lazy:diff(DefaultT1, Bdd)
                end, M2_orig),

  % M1 and M2 are disjunct
  {bdd_lazy:diff(DefaultT1, DefaultT2), maps:merge(M1, M2)}.





% ===========================
% BDD set-theoretic predicates
% ==================

% ===============
% emptiness check
is_empty(SnT, Symtab, Memo) ->
  Memoized = fun (Type, M, Fun) ->
    case sets:is_element(Type, M) of
      true ->
        true;
      _ ->
        NewMemo = sets:add_element(Type, M),
        Fun(NewMemo)
    end
             end,

  is_empty_atoms(SnT#ty.atoms, [], [], Symtab)
    andalso is_empty_special(SnT#ty.special, [], [], Symtab)
    andalso is_empty_ranges(SnT#ty.ints, [], [], Symtab)
    andalso Memoized(SnT#ty.list, Memo, fun (NewMemo) -> is_empty_list(SnT#ty.list, any(), any(), [], [], [], Symtab, NewMemo) end)
    andalso Memoized(SnT#ty.prod, Memo, fun (NewMemo) -> is_empty_multi_prod(SnT#ty.prod, [], [], Symtab, NewMemo) end)
    andalso Memoized(SnT#ty.arrw, Memo, fun (NewMemo) -> is_empty_multi_arrow(SnT#ty.arrw, [], [], Symtab, NewMemo) end).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               ATOMS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%intersected with empty is always empty
is_empty_atoms({bdd, 0}, _P, _N, _) -> true;
is_empty_atoms({bdd, 1}, P, N, _) ->
  PAtoms = case P of [] -> rep_basic:any(); _ -> rep_basic:finite(P) end,
  NAtoms = case N of [] -> rep_basic:any(); _ -> rep_basic:cofinite(N) end,
  I = rep_basic:intersect(PAtoms, NAtoms),
  rep_basic:is_empty(I);

% explore DNF branches
is_empty_atoms({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, P, N, Sym) ->
  Ty = find_ty(Ref, Args, atom, Sym),
  is_empty_atoms(bdd_lazy:intersect(Left, Ty), P, N, Sym)
    andalso is_empty_atoms(Middle, P, N, Sym)
    andalso is_empty_atoms(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), P, N, Sym);
% reduces to containment without variables
is_empty_atoms({bdd, {bdd_var, _Var}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_atoms(Left, P, N, Sym)
    andalso is_empty_atoms(Middle, P, N, Sym)
    andalso is_empty_atoms(Right, P, N, Sym);
is_empty_atoms({bdd, {bdd_atom, Atom}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_atoms(Left, P ++ [Atom], N, Sym)
    andalso is_empty_atoms(Middle, P, N, Sym)
    andalso is_empty_atoms(Right, P, N ++ [Atom], Sym).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               SPECIAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%intersected with empty is always empty
is_empty_special({bdd, 0}, _P, _N, _) -> true;
is_empty_special({bdd, 1}, P, N, _) ->
  Ps = lists:usort(P),
  Ns = lists:usort(N),

  length(Ps) > 1
    orelse
  length(Ns) == 5 % pid port ref float []
  orelse
    (length(Ps) == 1 andalso lists:member(lists:nth(1, Ps), Ns));

% explore DNF branches
is_empty_special({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, P, N, Sym) ->
  Ty = find_ty(Ref, Args, spec, Sym),
  is_empty_special(bdd_lazy:intersect(Left, Ty), P, N, Sym)
    andalso is_empty_special(Middle, P, N, Sym)
    andalso is_empty_special(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), P, N, Sym);
% reduces to containment without variables
is_empty_special({bdd, {bdd_var, _Var}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_special(Left, P, N, Sym)
    andalso is_empty_special(Middle, P, N, Sym)
    andalso is_empty_special(Right, P, N, Sym);
is_empty_special({bdd, {bdd_spec, Atom}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_special(Left, P ++ [Atom], N, Sym)
    andalso is_empty_special(Middle, P, N, Sym)
    andalso is_empty_special(Right, P, N ++ [Atom], Sym).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               RANGES (Integer)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%intersected with empty is always empty
is_empty_ranges({bdd, 0}, _P, _N, _Sym) -> true;
is_empty_ranges({bdd, 1}, P, N, _Sym) ->
  PInts = case P of [] -> [rep_ints:any()]; _ ->
    lists:map(fun({bdd_range, X, Y}) -> rep_ints:interval(X, Y) end, P)
          end,
  NInts = case N of [] -> [rep_ints:any()]; _ ->
    lists:map(fun({bdd_range, X, Y}) -> rep_ints:cointerval(X, Y) end, N)
          end,
  Pp = lists:foldl(fun rep_ints:intersect/2, rep_ints:any(), PInts),
  Nn = lists:foldl(fun rep_ints:intersect/2, rep_ints:any(), NInts),
  I = rep_ints:intersect(Pp, Nn),
  rep_ints:is_empty(I);
% explore DNF branches
is_empty_ranges({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, P, N, Sym) ->
  Ty = find_ty(Ref, Args, ints, Sym),
  is_empty_ranges(bdd_lazy:intersect(Left, Ty), P, N, Sym)
    andalso is_empty_ranges(Middle, P, N, Sym)
    andalso is_empty_ranges(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), P, N, Sym);
% reduces to containment without variables
is_empty_ranges({bdd, {bdd_var, _Var}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_ranges(Left, P, N, Sym)
    andalso is_empty_ranges(Middle, P, N, Sym)
    andalso is_empty_ranges(Right, P, N, Sym);
is_empty_ranges({bdd, Range = {bdd_range, _From, _To}, Left, Middle, Right}, P, N, Sym) ->
  is_empty_ranges(Left, P ++ [Range], N, Sym)
    andalso is_empty_ranges(Middle, P, N, Sym)
    andalso is_empty_ranges(Right, P, N ++ [Range], Sym).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               LISTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_empty_list({bdd, 0}, _Left, _Right, _Negated, _PVar, _NVar, _SymTab, _Memo) -> true;
is_empty_list({bdd, 1}, Left, Right, Negated, [], [], SymTab, Memo) ->
  % no more variables

  (is_empty(Left, SymTab, Memo)
    orelse is_empty(Right, SymTab, Memo)
    orelse explore_list(Left, Right, Negated, SymTab, Memo));

is_empty_list({bdd, 1}, Left, Right, Negated, PVars, [Var | NVars], SymTab, Memo) ->
  logger:debug("Removing negative variable from list clause: substitute in both positive and negative tuples:~n !~p => ~p", [Var, Var]),

  Map = #{ Var => stdtypes:tnegate(Var) },
  NsWithoutNegativeVars = [ {bdd_list, substitute_bdd(Map, A), substitute_bdd(Map, B)} || {bdd_list, A, B} <- Negated ],
  is_empty_list({bdd, 1}, substitute_bdd(Map, Left), substitute_bdd(Map, Right), NsWithoutNegativeVars, PVars, NVars, SymTab, Memo);
is_empty_list({bdd, 1}, Left, Right, Negated, [StdVar | PVars], [], SymTab, Memo) ->
  logger:debug("Removing positive variable from list clause~nsubstitute toplevel positive: ~n~p => (y1..yn)~nsubstitute negative and positive components: ~n~p => (y1..yn) U ~p", [StdVar, StdVar, StdVar]),

  {Avar, Bvar} = {fresh_variable(StdVar), fresh_variable(StdVar)},
  SubstitutionStdMap = #{StdVar => stdtypes:tunion([StdVar, stdtypes:tlist_improper(Avar, Bvar)]) },

  % covariance of lists: intersect left/right with (v1, v2)
  LeftNew = intersect(norm(Avar), Left),
  RightNew = intersect(norm(Bvar), Right),

  NNoVars = [ {bdd_list, substitute_bdd(SubstitutionStdMap, S), substitute_bdd(SubstitutionStdMap, T)}
    || {bdd_list, S, T} <- Negated ],

  % continue removing positive variables
  is_empty_list({bdd, 1}, LeftNew, RightNew, NNoVars, PVars, [], SymTab, Memo);

is_empty_list({bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
  Ty = find_ty(Ref, Args, list, SymTab),

  is_empty_list(bdd_lazy:intersect(Left, Ty), LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
    is_empty_list(bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), LL, RR, Negated, PVar, NVar, SymTab, Memo);
% collecting variables
is_empty_list({bdd, {bdd_var, Var}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
  is_empty_list(Left, LL, RR, Negated, PVar ++ [stdtypes:tvar(Var)], NVar, SymTab, Memo) andalso
    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
    is_empty_list(Right, LL, RR, Negated, PVar, NVar ++ [stdtypes:tvar(Var)], SymTab, Memo);
is_empty_list({bdd, {bdd_list, A, B}, Left, Middle, Right}, LL, RR, Negated, PVar, NVar, SymTab, Memo) ->
  %% norming
  is_empty_list(Left, intersect(A, LL), intersect(B, RR), Negated, PVar, NVar, SymTab, Memo) andalso
    is_empty_list(Middle, LL, RR, Negated, PVar, NVar, SymTab, Memo) andalso
    is_empty_list(Right, LL, RR, Negated ++ [{bdd_list, A, B}], PVar, NVar, SymTab, Memo).

explore_list(_S1, _S2, [], _SymTab, _Memo) -> false;
explore_list(S1, S2, [{bdd_list, T1, T2} | N], Symtab, Memo) ->
  ((subty:is_subty_bdd(S1, T1, Symtab, Memo) orelse explore_list(ty_rec:diff(S1, T1), S2, N, Symtab, Memo))
    andalso
    (subty:is_subty_bdd(S2, T2, Symtab, Memo) orelse explore_list(S1, ty_rec:diff(S2, T2), N, Symtab, Memo))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               TUPLES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_empty_multi_prod({{bdd, 1}, _}, _PVar, _NVar, _Symtab, _Memo) -> false;
% TODO I *think* multi-product resolves to the case without variables
is_empty_multi_prod({{bdd, 0}, Tuples}, _PVar, _NVar, Symtab, Memo) ->
  IsNTupleEmpty = fun
                    (_, _, false) -> false;
                    (Length, Bdd, _) ->
                      is_empty_n_prod(Length, Bdd, Symtab, Memo)
                    end,
  maps:fold(IsNTupleEmpty, true, Tuples);
is_empty_multi_prod({{bdd, {bdd_var, Var}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
  is_empty_multi_prod({L, T}, PVar ++ [Var], NVar, Symtab, Memo)
    andalso is_empty_multi_prod({M, T}, PVar, NVar, Symtab, Memo)
    andalso is_empty_multi_prod({R, T}, PVar, NVar ++ [Var], Symtab, Memo);
is_empty_multi_prod({{bdd, {bdd_named, {Ref, Args}}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
  {ok, Ty} = symtab:find_ty(Ref, Symtab),
  ActualTy = replace(Ty, Args),
  Only = pi(prod_default, norm(ActualTy)),

  %% non-default products need to be included in their respective partitions
  {_, More} = (norm(ActualTy))#ty.prod,
  Keys = lists:usort(maps:keys(More) ++ maps:keys(T)),

  % for a key
  NewT = maps:from_list([{Key,
      bdd_lazy:intersect(
        % Default is not ANY!
        % if tuple is not contained in current mapping, use default value mapping!
        maps:get(Key, T, L),
        maps:get(Key, More, bdd_lazy:any())
      )
  } || Key <- Keys]),

  NewNegT = maps:from_list([{Key, bdd_lazy:intersect(
    maps:get(Key, T, R),
    bdd_lazy:negate(maps:get(Key, More, bdd_lazy:any()))
  )} || Key <- Keys]),

  is_empty_multi_prod({bdd_lazy:intersect(L, Only), NewT}, PVar, NVar, Symtab, Memo)
    andalso
    is_empty_multi_prod({M, T}, PVar, NVar, Symtab, Memo)
    andalso
    is_empty_multi_prod({bdd_lazy:intersect(R, bdd_lazy:negate(Only)), NewNegT}, PVar, NVar, Symtab, Memo)
.

is_empty_n_prod(Length, Bdd, Symtab, Memo) ->
  is_empty_prod(Length, Bdd, [ty_rec:any() || _ <- lists:seq(1, Length)], [], [], [], Symtab, Memo).

is_empty_prod(_Length, {bdd, 0}, _Ps, _PVar, _NVar, _Ns, _SymTab, _Memo) -> true;
is_empty_prod(_Length, {bdd, 1}, PositiveComponents, [], [], N, SymTab, Memo) ->
  % no more variables
  % assertion
  Length = length(PositiveComponents),

  PositivesEmpty = lists:foldl(fun(Element, Result) -> Result orelse ty_rec:is_empty(Element, SymTab, Memo) end, false, PositiveComponents),
  PositivesEmpty orelse explore_tuple(Length, PositiveComponents, N, SymTab, Memo);
is_empty_prod(Length, {bdd, 1}, Ps, PVars, [Var | NVars], N, SymTab, Memo) ->
  logger:debug("Removing negative variable from product clause: substitute in both positive and negative tuples:~n !~p => ~p", [Var, Var]),

  Map = #{ Var => stdtypes:tnegate(Var) },

  PsWithoutNegativeVars = [ substitute_bdd(Map, P) || P <- Ps ],
  NsWithoutNegativeVars = [ {bdd_tuple, [substitute_bdd(Map, P) || P <- Components ]}
    || {bdd_tuple, Components} <- N ],

  is_empty_prod(Length, {bdd, 1}, PsWithoutNegativeVars, PVars, NVars, NsWithoutNegativeVars, SymTab, Memo);
is_empty_prod(Length, {bdd, 1}, Ps, [StdVar | PVars], [], N, SymTab, Memo) ->
  logger:debug("Removing positive variable from product clause~nsubstitute toplevel positive: ~n~p => (y1..yn)~nsubstitute negative and positive components: ~n~p => (y1..yn) U ~p", [StdVar, StdVar, StdVar]),

  FreshVars = [fresh_variable(StdVar) || _ <- lists:seq(1, Length) ],
  SubstitutionStdMap = #{StdVar => stdtypes:tunion([StdVar, stdtypes:ttuple(FreshVars)]) },

  SubstitutedPositiveTupleComponents = [substitute_bdd(SubstitutionStdMap, C) || C <- Ps],

  % covariance of tuples: intersect positives with (y1..yn)
  FinishedPosTuple = [intersect(norm(Var), C)|| {Var, C} <- lists:zip(FreshVars, SubstitutedPositiveTupleComponents)],

  NNoVars = [ {bdd_tuple, [substitute_bdd(SubstitutionStdMap, C) || C <- Components]}
    || {bdd_tuple, Components} <- N ],

  % continue removing positive variables
  is_empty_prod(Length, {bdd, 1}, FinishedPosTuple, PVars, [], NNoVars, SymTab, Memo);

is_empty_prod(Length, {bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
  Ty = find_ty(Ref, Args, {prod, Length}, SymTab),

  is_empty_prod(Length, bdd_lazy:intersect(Left, Ty),   Ps, PVar, NVar, N, SymTab, Memo) andalso
    is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
    is_empty_prod(Length, bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)),  Ps, PVar, NVar, N, SymTab, Memo);
% collecting variables
is_empty_prod(Length, {bdd, {bdd_var, Var}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
  is_empty_prod(Length, Left,   Ps, PVar ++ [stdtypes:tvar(Var)], NVar, N, SymTab, Memo) andalso
    is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
    is_empty_prod(Length, Right,  Ps, PVar, NVar ++ [stdtypes:tvar(Var)], N, SymTab, Memo);
is_empty_prod(Length, {bdd, {bdd_tuple, BddComponents}, Left, Middle, Right}, Ps, PVar, NVar, N, SymTab, Memo) ->
  %% norming
  PsExtended = [ty_rec:intersect(ToIntersect, Others) || {ToIntersect, Others} <- lists:zip(BddComponents, Ps)],

  is_empty_prod(Length, Left,   PsExtended, PVar, NVar, N, SymTab, Memo) andalso
  is_empty_prod(Length, Middle, Ps, PVar, NVar, N, SymTab, Memo) andalso
  is_empty_prod(Length, Right,  Ps, PVar, NVar, N ++ [{bdd_tuple, BddComponents}], SymTab, Memo).

explore_tuple(_L, _Ps, [], _Symtab, _Memo) -> false;
explore_tuple(L, Ps, [{bdd_tuple, NegativeBddComponents} | N], Symtab, Memo) ->
  Solve = fun({Index, {PComponent, NComponent}}, Result) ->
    Result
      andalso
      begin
        subty:is_subty_bdd(PComponent, NComponent, Symtab, Memo)
          orelse
          % remove pi_Index(NegativeComponents) from pi_Index(PComponents) and continue searching
        begin
          DoDiff = fun({IIndex, PComp}) ->
            case IIndex of
              Index -> ty_rec:diff(PComp, NComponent);
              _ -> PComp
            end
                   end,
          NewPs = lists:map(DoDiff, lists:zip(lists:seq(1, length(Ps)), Ps)),
          explore_tuple(L, NewPs, N, Symtab, Memo)
        end
      end
          end,


  lists:foldl(Solve, true, lists:zip(lists:seq(1, L), lists:zip(Ps, NegativeBddComponents))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_empty_multi_arrow({{bdd, 1}, _}, _PVar, _NVar, _Symtab, _Memo) -> false;
% TODO I *think* multi-arrow resolves to the case without variables
is_empty_multi_arrow({{bdd, 0}, Arrows}, _PVar, _NVar, Symtab, Memo) ->
  IsNArrowEmpty = fun
                    (_, _, false) -> false;
                    (Length, Bdd, _) ->
                      is_empty_n_arrow(Length, Bdd, Symtab, Memo)
                  end,
  maps:fold(IsNArrowEmpty, true, Arrows);
is_empty_multi_arrow({{bdd, {bdd_var, Var}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
  is_empty_multi_arrow({L, T}, PVar ++ [Var], NVar, Symtab, Memo)
    andalso is_empty_multi_arrow({M, T}, PVar, NVar, Symtab, Memo)
    andalso is_empty_multi_arrow({R, T}, PVar, NVar ++ [Var], Symtab, Memo);
is_empty_multi_arrow({{bdd, {bdd_named, {Ref, Args}}, L, M, R}, T}, PVar, NVar, Symtab, Memo) ->
  {ok, Ty} = symtab:find_ty(Ref, Symtab),
  ActualTy = replace(Ty, Args),
  Only = pi(arrw_default, norm(ActualTy)),

  %% non-default arrows need to be included in their respective partitions
  {_, More} = (norm(ActualTy))#ty.arrw,
  Keys = lists:usort(maps:keys(More) ++ maps:keys(T)),

  % for a key
  NewT = maps:from_list([{Key, bdd_lazy:intersect(
    % Default is not ANY!
    % if tuple is not contained in current mapping, use default value mapping!
    maps:get(Key, T, L),
    maps:get(Key, More, bdd_lazy:any())
  )} || Key <- Keys]),

  NewNegT = maps:from_list([{Key, bdd_lazy:intersect(
    maps:get(Key, T, R),
    bdd_lazy:negate(maps:get(Key, More, bdd_lazy:any()))
  )} || Key <- Keys]),

  is_empty_multi_arrow({bdd_lazy:intersect(L, Only), NewT}, PVar, NVar, Symtab, Memo)
    andalso is_empty_multi_arrow({M, T}, PVar, NVar, Symtab, Memo)
    andalso is_empty_multi_arrow({bdd_lazy:intersect(R, bdd_lazy:negate(Only)), NewNegT}, PVar, NVar, Symtab, Memo).

is_empty_n_arrow(Length, Bdd, Symtab, Memo) ->
  is_empty_arrow(Length, Bdd, ty_rec:empty(), [], [], [], [], Symtab, Memo).

is_empty_arrow(_Length, {bdd, 0}, _STys, _P, _N, _PVars, _NVars, _SymTab, _Memo) -> true;
is_empty_arrow(Length, {bdd, 1}, STys, P, N, PVars, [Var | NVars], SymTab, Memo) ->
  logger:debug("Removing negative variable from fun clause: substitute in both positive and negative funs:~n !~p => ~p", [Var, Var]),

  Map = #{ Var => stdtypes:tnegate(Var) },
  SWithoutNeg = substitute_bdd(Map, STys),

  PWithoutNeg =
    [ {bdd_fun_full, [substitute_bdd(Map, C) || C <- Components ], substitute_bdd(Map, Ret)}
    || {bdd_fun_full, Components, Ret} <- P ],

  NWithoutNeg =
    [ {bdd_fun_full, [substitute_bdd(Map, C) || C <- Components ], substitute_bdd(Map, Ret)}
      || {bdd_fun_full, Components, Ret} <- N ],

  is_empty_arrow(Length, {bdd, 1}, SWithoutNeg, PWithoutNeg, NWithoutNeg, PVars, NVars, SymTab, Memo);
is_empty_arrow(Length, {bdd, 1}, STys, P, N, [Var | PVars], [], SymTab, Memo) ->
  logger:debug("Removing positive variable from tuple clause~nsubstitute toplevel positive: ~n~p", [STys]),

  AnyArgs = [stdtypes:tany() || _ <- lists:seq(1, Length) ],
  % "alpha1"
  FreshArgVars = [fresh_variable(Var) || _ <- lists:seq(1, Length) ],
  % alpha2
  FreshRetVars = fresh_variable(Var),

  % ========
  % PART 1
  % replace var by alpha1 -> alpha2 intersection

  % substitution
  % alpha   =>  (alpha1 -> alpha2) U alpha
  Phi1 = #{ Var => stdtypes:tunion([stdtypes:tfun_full(FreshArgVars, FreshRetVars), Var]) },

  % add alpha1 to union of domains
  T1 = tuple_of(FreshArgVars),
  NewS = ty_rec:union(T1, STys),

  % substitute negative and positive funs
  NewPos = [ {bdd_fun_full, [substitute_bdd(Phi1, C) || C <- Components ], substitute_bdd(Phi1, Ret)}
    || {bdd_fun_full, Components, Ret} <- P ],
  NewNeg = [ {bdd_fun_full, [substitute_bdd(Phi1, C) || C <- Components ], substitute_bdd(Phi1, Ret)}
    || {bdd_fun_full, Components, Ret} <- N ],

  % ========
  % PART 2
  % replace var by alpha1 -> alpha2 intersection

  EleArrow = stdtypes:tintersect([
      stdtypes:tfun_full(FreshArgVars, FreshRetVars),
      stdtypes:tnegate(stdtypes:tfun_full(AnyArgs, stdtypes:tnone()))
    ]),
  % substitution
  % alpha   =>  [(alpha1 -> alpha2) \ (1 -> 0)] U alpha
  Phi2 = #{ Var => stdtypes:tunion([EleArrow , Var]) },

  % add alpha1 to union of domains (alpha1 and empty set, so just alpha1)
  T2 = tuple_of(FreshArgVars),
  NewS2 = ty_rec:union(T2, STys),

  % substitute negative and positive funs
  NewPos2 = [ {bdd_fun_full, [substitute_bdd(Phi2, C) || C <- Components ], substitute_bdd(Phi2, Ret)}
    || {bdd_fun_full, Components, Ret} <- P ],
  NewNeg2 = [ {bdd_fun_full, [substitute_bdd(Phi2, C) || C <- Components ], substitute_bdd(Phi2, Ret)}
    || {bdd_fun_full, Components, Ret} <- N ],

  % both part 1 and part 2 have to hold
  is_empty_arrow(Length, {bdd, 1}, NewS, NewPos, NewNeg, PVars, [], SymTab, Memo)
    andalso
    is_empty_arrow(Length, {bdd, 1}, NewS2, NewPos2, NewNeg2, PVars, [], SymTab, Memo);
is_empty_arrow(_Length, {bdd, 1}, _STys, _P, [], [], [], _SymTab, _Memo) -> false;
% solve arrow without vars
is_empty_arrow(Length, {bdd, 1}, STyRec, PBddLazys, [{bdd_fun_full, NTs1, NT2} | NBddsLazy ], [], [], SymTab, Memo) ->
    (
        begin
          % treat multi argument as tuple
        FunTuple = tuple_of(NTs1),

        %% ∃ NTys1 --> T2 ∈ N s.t.
        %%    NTys1 are in the domains of the function (as a tuple)
        %%    S is the union of all (tuple) domains of the positive function intersections
        subty:is_subty_bdd(FunTuple, STyRec, SymTab, Memo)
        end
          andalso
          explore_arrow(FunTuple, NT2, PBddLazys, ty_rec:empty(), ty_rec:any(), SymTab, Memo)
    )
      %% Continue searching for another arrow ∈ N
      orelse is_empty_arrow(Length, {bdd, 1}, STyRec, PBddLazys, NBddsLazy, [], [], SymTab, Memo);

is_empty_arrow(Length, {bdd, {bdd_named, {Ref, Args}}, Left, Middle, Right}, S, P, N, PVar, NVar, SymTab, Memo) ->
  Ty = find_ty(Ref, Args, {arrw, Length}, SymTab),

  is_empty_arrow(Length, bdd_lazy:intersect(Left, Ty), S, P, N, PVar, NVar, SymTab, Memo) andalso
    is_empty_arrow(Length, Middle, S, P, N, PVar, NVar, SymTab, Memo) andalso
    is_empty_arrow(Length, bdd_lazy:intersect(Right, bdd_lazy:negate(Ty)), S, P, N, PVar, NVar, SymTab, Memo);
is_empty_arrow(Length, {bdd, {bdd_var, Var}, Left, Middle, Right}, S, P, N, PVars, NVars, SymTab, Memo) ->
  is_empty_arrow(Length, Left, S, P, N, PVars ++ [stdtypes:tvar(Var)], NVars, SymTab, Memo) andalso
    is_empty_arrow(Length, Middle, S, P, N, PVars, NVars, SymTab, Memo) andalso
    is_empty_arrow(Length, Right, S, P, N, PVars, NVars  ++ [stdtypes:tvar(Var)], SymTab, Memo);
is_empty_arrow(Length, {bdd, Arrw = {bdd_fun_full, T1raw, _}, L, M, R}, S, P, N, PVars, NVars, SymTab, Memo) ->
  T1 = tuple_of(T1raw),
  is_empty_arrow(Length, L, ty_rec:union(S, T1), [Arrw] ++ P, N, PVars, NVars, SymTab, Memo)
    andalso is_empty_arrow(Length, M, S, P, N, PVars, NVars, SymTab, Memo)
    andalso is_empty_arrow(Length, R, S, P, [Arrw] ++ N, PVars, NVars, SymTab, Memo).

explore_arrow(T1, T2, [], Domain, Codomain, SymTab, Memo) ->
  subty:is_subty_bdd(T1, Domain, SymTab, Memo) orelse subty:is_subty_bdd(Codomain, T2, SymTab, Memo);
explore_arrow(T1, T2, [{bdd_fun_full, S1raw, S2} | P], Domain, Codomain, SymTab, Memo) ->
  S1 = tuple_of(S1raw),
  explore_arrow(T1, T2, P, Domain, ty_rec:intersect(Codomain, S2), SymTab, Memo)
    andalso
    explore_arrow(T1, T2, P, ty_rec:union(Domain, S1), Codomain, SymTab, Memo).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%               UTILITY FUNCTIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

substitute_bdd(StdMap, #ty{
  atoms = Atoms, special = S, list = Lists, ints = Ints, prod = {DefaultTuple, Tuples}, arrw = {DefaultFun, Funs}
}) ->
  % substitutions can introduce tuples and arrows which are currently not captured by (non-default) Tuples and Arrows
  % figure out what length to explicitly calculate with the DefaultTuple value to do an explicit substitution filtering
  % TODO do this only once
  ProdLengths = lists:usort(lists:flatten([begin Ty = norm(Target), #ty{prod = {_, Others}} = Ty, maps:keys(Others) end || {_V, Target} <- maps:to_list(StdMap)])),
  FunLengths = lists:usort(lists:flatten([begin Ty = norm(Target), #ty{arrw = {_, Others}} = Ty, maps:keys(Others) end || {_V, Target} <- maps:to_list(StdMap)])),


  % TODO smart ty constructor
  % whenever default Value matches the value in the tuple/fun map, remove the value in the tuple/fun map (redundant)
  #ty{
    atoms = bdd_lazy:substitute(atom, Atoms, StdMap),
    ints = bdd_lazy:substitute(ints, Ints, StdMap),
    special = bdd_lazy:substitute(spec, S, StdMap),
    list = bdd_lazy:substitute(list, Lists, StdMap),
    prod =
    {bdd_lazy:substitute(prod_default, DefaultTuple, StdMap),
      maps:merge(
        maps:from_list([{N, bdd_lazy:substitute({prod, N}, DefaultTuple, StdMap)} || N <- ProdLengths]),
        maps:map(fun(Length, V) -> bdd_lazy:substitute({prod, Length}, V, StdMap) end, Tuples) % this map supersedes the default value substitutions
      )
    },
    arrw =
    {bdd_lazy:substitute(arrw_default, DefaultFun, StdMap),
      maps:merge(
        maps:from_list([{N, bdd_lazy:substitute({arrw, N}, DefaultFun, StdMap)} || N <- FunLengths]),
        maps:map(fun(Length, V) -> bdd_lazy:substitute({arrw, Length}, V, StdMap) end, Funs) % this map supersedes the default value substitutions
      )
    }
  }.

fresh_variable({Type, VariableName}) ->
  Uniq = erlang:unique_integer(),
  ToName = lists:takewhile(fun(E) -> not(E == $-) end, atom_to_list(VariableName)),

  {Type,
    %% behold the universally feared dynamically created Erlang atom
    list_to_atom(
      ToName ++ erlang:integer_to_list(Uniq)
    )
  }.

tuple_of(Components) ->
  Tuple = #{length(Components) => bdd_lazy:pos({bdd_tuple, Components})},
  (empty())#ty{prod = {bdd_lazy:empty(), Tuple}}.

pi(atom, #ty{atoms = A}) -> A;
pi(ints, #ty{ints = A}) -> A;
pi(spec, #ty{special = A}) -> A;
pi(list, #ty{list = A}) -> A;
pi(prod_default, #ty{prod = {Default, _}}) -> Default;
pi(arrw_default, #ty{arrw = {Default, _}}) -> Default;
pi({prod, Length}, #ty{prod = {_, Prods}}) -> maps:get(Length, Prods);
pi({arrw, Length}, #ty{arrw = {_, Arrws}}) -> maps:get(Length, Arrws).

find_ty(Ref, Args, Type, Sym) ->
  % 1: lookup
  {ok, Ty} = symtab:find_ty(Ref, Sym),
  % 2: replace ty scheme variables with argument variables
  ActualTy = replace(Ty, Args),
  % 3: norm and project out type
  pi(Type, norm(ActualTy)).

replace({ty_scheme, Vars, Ty}, Args) ->
  Vs = [Name || {Name, _} <- Vars],
  Subst = maps:from_list(lists:zip(Vs, Args)),
  SubTy = subst:apply(Subst, Ty),
  SubTy.