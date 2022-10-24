-module(prop_opt_set).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-import(stdtypes, [tfun_full/2, ttuple/1, tintersect/1, tunion/1, tnegate/1]).

prop_generator_quality() ->
  ?FORALL(X, limited_ast(),
    begin
      % io:format("~n~p~n", [X]),
      collect(
        case { equiv(X, {predef, none}), equiv(X, {predef, any}) } of
          {true, false} -> empty;
          {false, true} -> any;
          {false, false} ->
            case
              {
                equiv(X, stdtypes:tatom()),
                equiv(X, stdtypes:tint()),
                equiv(X, {tuple_any}),
                equiv(X, {fun_simple})
              } of
              {true, false, false, false} -> any_basic;
              {false, true, false, false} -> any_interval;
              {false, false, true, false} -> any_product;
              {false, false, false, true} -> any_arrow;
              {false, false, false, false} -> non_trivial
            end
        end, true)
    end
  ).

prop_norm_identity() ->
  ?FORALL(Ty, limited_ast(),
    begin
      Ty2 = ty_rec:eval(ty_rec:norm(Ty)),
      equiv(Ty, Ty2)
    end
  ).

prop_trivial_set_operations() ->
  ?FORALL(Ty, limited_ast(),
    conjunction([
      {any_intersection, any_intersect(Ty)},
      {empty_intersection, empty_intersect(Ty)},
      {any_union, any_union(Ty)},
      {empty_union, empty_union(Ty)},
      % TODO move this out of FORALL
      {trivial_negation, trivial_negation()}
    ])
  ).

%% TODO this property does not hold anymore
%%      what to do with bdds with tuples/funs which have the same default value? => smart constructor maybe
%%prop_basic_minimal_representation() ->
%%  ?FORALL({B1, B2}, {limited_basic_ast(), limited_basic_ast()},
%%    begin
%%      ?IMPLIES(
%%        bdd_rec:norm(B1) /= bdd_rec:norm(B2)
%%          andalso non_trivial_basic(B1)
%%          andalso non_trivial_basic(B2),
%%        (not subtype(B1, B2) orelse not subtype(B2, B1))
%%      )
%%    end
%%  ).

%% TODO multiple arguments testing
prop_any_arrow() ->
  ?FORALL(A, tfun_full([limited_ast()], limited_ast()), subtype(A, {fun_simple}) ).

prop_any_arrow_ext() ->
  ?FORALL({A, C}, {tfun_full([limited_ast()], limited_ast()), limited_ast()}, subtype(A, tfun_full([{predef, none}], C)) ).

%%prop_arrow_never_atom() ->
%%  ?FORALL({A, B}, {tfun_full(limited_ast(), limited_ast()), frequency([{1, stdtypes:tatom()}, {5, stdtypes:tatom(common_atoms())}])},
%%    not subtype(A, B)
%%  ).

%%prop_arrow_never_interval() ->
%%  ?FORALL({A, Int}, {arrow(limited_ast(), limited_ast()), interval(any_int(), any_int())},
%%    ?IMPLIES( not empty(A), not subtype(A, Int) )
%%  ).

%% TODO multi tuple
prop_fun_never_tuple() ->
  ?FORALL({A, P}, {tfun_full([limited_ast()], limited_ast()), ttuple([limited_ast(), limited_ast()])},
    begin
      ?IMPLIES( not empty(A), not subtype(A, P) )
    end
  ).

%% TODO multi arrow
prop_arrow_never_empty() ->
  ?FORALL(A, tfun_full([limited_ast()], limited_ast()), not empty(A) ).

% S -> T & A -> T <=> (S U A) ->  T
prop_arrow_union_of_domains_when_same_codomain() ->
  ?FORALL({S, A, T}, {limited_ast(), limited_ast(), limited_ast()},
    begin
      A1 = tfun_full([S], T),
      A2 = tfun_full([A], T),
      A3 = tfun_full([tunion([S, A])], T),
      equiv(tintersect([A1, A2]), A3)
    end
    ).

prop_any_product() ->
  ?FORALL(A, ttuple([limited_ast(), limited_ast()]), subtype(A, {tuple_any}) ).

%%prop_empty_right_product() ->
%%  ?FORALL(A, product(limited_ast(), east:empty()), subtype(A, east:empty()) ).
%%
%%prop_empty_left_product() ->
%%  ?FORALL(A, product(east:empty(), limited_ast()), subtype(A, east:empty()) ).
%%
%%prop_product_never_basic() ->
%%  ?FORALL({A, B}, {product(limited_ast(), limited_ast()), frequency([{1, east:any_basic()}, {5, basic(common_atoms())}])},
%%    ?IMPLIES( not empty(A), not subtype(A, B) )
%%  ).
%%
%%prop_product_never_interval() ->
%%  ?FORALL({A, Int}, {product(limited_ast(), limited_ast()), interval(any_int(), any_int())},
%%    ?IMPLIES( not empty(A), not subtype(A, Int) )
%%  ).
%%
%%prop_product_never_arrow() ->
%%  ?FORALL({A, P}, {product(limited_ast(), limited_ast()), arrow(limited_ast(), limited_ast())},
%%    ?IMPLIES( not empty(A), not subtype(A, P) )
%%  ).
%%
%%% found bug in old impl related to ANY_BASIC
%%prop_equiv_to_old() ->
%%  ?FORALL({X, Y}, {limited_ast(), limited_ast()}, subtype(X, Y) =:= subtype_old(X, Y) ).
%%
%%% closed type intersected with type variable equiv to closed type
%%% S && alpha <: T iff S <: T
%%prop_closed_type_type_var() ->
%%  ?FORALL({S, T} , {limited_ast(), limited_ast()},
%%    begin
%%      SVar = east:intersect([S, east:var(alpha)]),
%%      R1 = subtype_old(SVar, T),
%%      R2 = subtype_old(S, T),
%%      R1 =:= R2
%%    end
%%  ).
%%
%%prop_minify_equiv() ->
%%  ?FORALL(X, limited_ast(), equiv(X, eminify:dnf_minify(X)) ).

prop_n_tuple_disjoint() ->
  ?FORALL({TupleA = {tuple, ComponentsA}, TupleB = {tuple, ComponentsB}},
    {
      ?LET(SizeA, range(1,10), {tuple, [limited_ast() || _ <- lists:seq(1, SizeA)]}),
      ?LET(SizeB, range(1,10), {tuple, [limited_ast() || _ <- lists:seq(1, SizeB)]})
    },
    ?IMPLIES(
      % sizes are different
      (size_of(TupleA) /= size_of(TupleB))
        andalso
        % none of the components are empty
      lists:all(fun(E) -> E end, [not subtype(Component, {predef, none}) || Component <- ComponentsA ++ ComponentsB])
      ,
      % then tuples are not comparable
      (not subtype(TupleA, TupleB)) andalso (not subtype(TupleB, TupleA))
    )
  ).

size_of({tuple, C}) -> length(C).

common_atoms() ->
  oneof([a,b,c,d,e,f,g,'1','2', atom()]). % only sometimes use an uncommon atom

limited_ast() ->
  ?SIZED(Size, limited_ast(Size)).

%%limited_basic_ast() ->
%%  ?SIZED(Size, limited_basic_ast(Size)).

%%limited_basic_ast(Size) when Size =< 1 ->
%%  frequency([
%%    {1, stdtypes:tatom()},
%%    {10, stdtypes:tatom(common_atoms())}
%%  ]);
%%limited_basic_ast(Size) ->
%%  frequency([
%%    {10, unbalanced_binary_op(Size, fun cut_limited_basic_ast/1, [union, intersection], 6)},
%%    {5, {negation, limited_basic_ast(Size-1)}}
%%  ]).


limited_ast(Size) when Size =< 1 ->
  frequency([
    {1, stdtypes:tatom()},
    {10, stdtypes:tatom(common_atoms())},
    {2, {predef, any}},
    {1, {predef, none}},
    {1, {tuple_any}},
    {1, {predef, integer}},
    {1, {fun_simple}}
%%    {3, east:any_interval()},
%%    {1, east:any_arrow()},
  ]);
limited_ast(Size) ->
  frequency([
%%    {10, unbalanced(Size, function)},
    {20, unbalanced_binary_op(Size, fun cut_limited_ast/1, [union, intersection, tuple], 2)},
    {10, unbalanced_binary_op(Size, fun cut_limited_ast/1, [union, intersection, tuple], 6)},
    {10, {negation, (limited_ast(Size-1))}}
]).

cut_limited_ast(Size) ->
  ?LET(CutSize, range(2, Size), limited_ast(Size div CutSize)).

%%cut_limited_basic_ast(Size) ->
%%  ?LET(CutSize, range(2, Size), limited_basic_ast(Size div CutSize)).

unbalanced_binary_op(Size, Elements, Types, LimitRank) -> ?LAZY(
  begin
    RandomOp = oneof(Types),
    MaxRank = LimitRank,
    Options = [
        {((MaxRank * 10) div Rank),
          {RandomOp, [ Elements(Size) || _ <- lists:seq(1, Rank)]}
        }
      || Rank <- lists:seq(1,MaxRank)
    ],
    frequency(Options ++ [{1, {RandomOp, []}}]) % empty union/intersect edge case
  end
).

%%any_int() -> oneof(['*', integer()]).
%%non_trivial_basic(B) ->
%%  % not empty and not ANY_BASIC
%%  (not subtype(B, east:empty()))
%%    andalso
%%    (not subtype(east:any_basic(), B)).
%%
%%
trivial_negation() ->
  T = (tnegate(stdtypes:empty())),
  T2 = (tnegate(stdtypes:any())),
  equiv(T, stdtypes:any()) andalso equiv(T2, stdtypes:empty()).

any_intersect(Ty) ->
  T2 = (tintersect([stdtypes:any(), Ty])),
  T3 = (tintersect([Ty, stdtypes:any()])),
  equiv(T2, Ty) andalso equiv(T3, Ty).

empty_intersect(Ty) ->
  T2 = (tintersect([stdtypes:empty(), Ty])),
  T3 = (tintersect([Ty, stdtypes:empty()])),
  equiv(T2, stdtypes:empty()) andalso equiv(T3, stdtypes:empty()).

any_union(Ty) ->
  T2 = (tunion([stdtypes:any(), Ty])),
  T3 = (tunion([Ty, stdtypes:any()])),
  equiv(T2, stdtypes:any()) andalso equiv(T3, stdtypes:any()).

empty_union(Ty) ->
  T2 = (tunion([stdtypes:empty(), Ty])),
  T3 = (tunion([Ty, stdtypes:empty()])),
  equiv(T2, Ty) andalso equiv(T3, Ty).


equiv(S, T) ->
  subtype(S, T) andalso
    subtype(T, S).

%%
%%equiv2(S, T) ->
%%  subtype_old(S, T) andalso
%%    subtype_old(T, S).
%%
empty(S) ->
  equiv(S, {predef, none}).

subtype(S, T) ->
  subty:is_subty(none, S, T).
