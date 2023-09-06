-module(prop_subty).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-export([limited_ast/0]).

limited_interval() ->
  ?LAZY(?LET(Interval, prop_interval:limited_interval(), ty_rec:interval(dnf_var_int:int(Interval)))).

limited_atom() ->
  ?LAZY(?LET(Atom, oneof([a,b,c,d,e,f,g,h,i,j, atom()]), ty_rec:atom(dnf_var_ty_atom:ty_atom(ty_atom:finite([Atom]))))).

limited_function() -> ?SIZED(Size, limited_function(Size)).
limited_function(Size) ->
  ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)},
    ty_rec:function(dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(A, B))))
  )).

limited_tuple() -> ?SIZED(Size, limited_tuple(Size)).
limited_tuple(Size) ->
  ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)},
    ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([A, B]))))
  )).


limited_ast() ->
  ?SIZED(Size, limited_ast(Size)).

limited_ast(Size) when Size =< 1 ->
  frequency([
    % intervals
    {4, limited_interval()},
    % atoms
    {5, limited_atom()},
    {1, ?LAZY(ty_rec:atom())},
    {1, ?LAZY(ty_rec:tuple())},
    {1, ?LAZY(ty_rec:function())},

    % any & empty
    {1, ?LAZY(ty_rec:any())},
    {1, ?LAZY(ty_rec:empty())}
  ]);
limited_ast(Size) ->
  frequency([
    % tuples TODO unbalanced ASTs (left right uneven)
    {5, ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)},
        ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([A, B]))))
    ))},

    % functions
    {3, limited_function(Size)},

    {4, ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)}, ty_rec:union(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)}, ty_rec:intersect(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_ast(Size div 2), limited_ast(Size div 2)}, ty_rec:diff(A, B)))  },
    {3, ?LAZY(?LET(Compound, limited_ast(Size - 1), ty_rec:negate(Compound)))  }
  ]).

% limited_ast() should generate at least 70% non-trivial types
prop_generator_quality() ->
  ?FORALL(X, limited_ast(),
    begin
%%      io:format("~n~p~n", [X]),
      collect(
        case { equiv(X, ty_rec:empty()), equiv(X, ty_rec:any()) } of
          {true, false} -> empty;
          {false, true} -> any;
          {false, false} ->
            case
              {
                equiv(X, ty_rec:atom()),
                equiv(X, ty_rec:interval()),
                equiv(X, ty_rec:tuple()),
                equiv(X, ty_rec:function())
              } of
              {true, false, false, false} -> any_basic;
              {false, true, false, false} -> any_interval;
              {false, false, true, false} -> any_product;
              {false, false, false, true} -> any_function;
              {false, false, false, false} -> non_trivial
            end
        end, true)
    end
  ).

prop_trivial_set_operations() ->
  ?FORALL(Ty, limited_ast(),
    conjunction([
      {any_intersection, any_intersect(Ty)},
      {empty_intersection, empty_intersect(Ty)},
      {any_union, any_union(Ty)},
      {empty_union, empty_union(Ty)}
    ])
  ).

any_intersect(Ty) ->
  T2 = ty_rec:intersect(ty_rec:any(), Ty),
  T3 = ty_rec:intersect(Ty, ty_rec:any()),
  equiv(T2, Ty) andalso equiv(T3, Ty) andalso equiv(T2, T3).

empty_intersect(Ty) ->
  T2 = ty_rec:intersect(ty_rec:empty(), Ty),
  T3 = ty_rec:intersect(Ty, ty_rec:empty()),
  equiv(T2, ty_rec:empty()) andalso equiv(T3, ty_rec:empty()) andalso equiv(T2, T3).

any_union(Ty) ->
  T2 = ty_rec:union(ty_rec:any(), Ty),
  T3 = ty_rec:union(Ty, ty_rec:any()),
  equiv(T2, ty_rec:any()) andalso equiv(T3, ty_rec:any()) andalso equiv(T2, T3).

empty_union(Ty) ->
  T2 = ty_rec:union(ty_rec:empty(), Ty),
  T3 = ty_rec:union(Ty, ty_rec:empty()),
  equiv(T2, Ty) andalso equiv(T3, Ty) andalso equiv(T2, T3).

prop_any_function() ->
  % any function A is included in the top arrow type
  ?FORALL( A, limited_function(), subtype(A, ty_rec:function()) ).

prop_function_never_empty() ->
  % any function A is never empty
  ?FORALL( A, limited_function(), not subtype(A, ty_rec:empty()) ).

prop_function_never_atom() ->
  ?FORALL({A, B}, {limited_function(), limited_atom()}, not subtype(A, B) ).

prop_function_never_interval() ->
  ?FORALL({A, B}, {limited_function(), limited_interval()}, not subtype(A, B) ).


prop_function_never_tuple() ->
  ?FORALL({F, T}, {limited_function(), limited_tuple()}, not subtype(F, T) ).

% S -> T & A -> T <=> (S U A) ->  T
prop_function_union_of_domains_when_same_codomain() ->
  ?FORALL({S, A, T}, {limited_ast(), limited_ast(), limited_ast()},
    begin
      A1 = ty_rec:function(S, T),
      A2 = ty_rec:function(A, T),
      A3 = ty_rec:function(ty_rec:union(S, A), T),
      equiv(ty_rec:intersect(A1, A2), A3)
    end
    ).

prop_any_tuple() ->
  ?FORALL(A, limited_tuple(), subtype(A, ty_rec:tuple()) ).

prop_empty_tuple() ->
  ?FORALL(A, limited_tuple(),
    begin
      Ty = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([ty_rec:empty(), A])))),
      Ty2 = ty_rec:tuple(2, dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple([A, ty_rec:empty()])))),
      subtype(Ty, ty_rec:empty()) andalso subtype(Ty2, ty_rec:empty())
    end
  ).

prop_tuple_never_atom_interval_function_if_not_empty() ->
  ?FORALL({A, B}, {limited_tuple(), oneof([limited_atom(), limited_interval(), limited_function()])},
    ?IMPLIES( not empty(A), not subtype(A, B) )
  ).


% closed type intersected with type variable equiv to closed type
% S && alpha <: T iff S <: T
prop_closed_type_type_var() ->
  ?FORALL({S, T} , {limited_ast(), limited_ast()},
    begin
      SVar = ty_rec:intersect(S, ty_rec:variable(ty_variable:new(alpha))),
      R1 = subtype(SVar, T),
      R2 = subtype(S, T),
      R1 =:= R2
    end
  ).

equiv(S, T) ->
  ty_rec:is_subtype(S, T) andalso
    ty_rec:is_subtype(T, S).

subtype(S, T) ->
  ty_rec:is_subtype(S, T).

empty(S) ->
  equiv(S, ty_rec:empty()).
