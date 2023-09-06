-module(prop_atom_normalize).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

limited_ty_atom() ->
  ?LET(TyAtom, limited_atom(), ty_rec:atom(dnf_var_ty_atom:ty_atom(TyAtom))).

limited_atom() ->
  ?SIZED(Size, limited_atom(Size)).

limited_atom(Size) when Size =< 1 ->
  frequency([
    {1, ?LAZY(ty_atom:any())},
    {1, ?LAZY(ty_atom:empty())},
    {5, ?LAZY(?LET(SingleAtom, oneof([a,b,c,d,e,f,g,h,i,j, atom()]), ty_atom:finite([SingleAtom])))}
  ]);
limited_atom(Size) ->
  frequency([
    {10, ?LAZY(?LET({A, B}, {limited_atom(Size div 2), limited_atom(Size div 2)}, ty_atom:union(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_atom(Size div 2), limited_atom(Size div 2)}, ty_atom:intersect(A, B)))  },
    {1, ?LAZY(?LET({A, B}, {limited_atom(Size div 2), limited_atom(Size div 2)}, ty_atom:diff(A, B)))  },
    {3, ?LAZY(?LET(CompoundInt, limited_atom(Size - 1), ty_atom:negate(CompoundInt)))  }
  ]).


% just atoms produce either satisfiable or unsatisfiable constraint sets
prop_only_atoms_either_sat_or_unsat() ->
  ?FORALL(X, limited_ty_atom(),
    begin
%%      io:format(user, "~p~n", [ty_ref:load(X)]),
      Result = ty_rec:normalize(X, sets:new(), sets:new()),
      Result =:= [] orelse Result =:= [[]]
    end
).

