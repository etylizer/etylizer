-module(dnf_ty_map).

-define(ATOM, ty_map).
-define(LEAF, ty_bool).
-define(NODE, ty_node).

-include("dnf/bdd.hrl").

-spec is_empty_line({[T], [T], ?LEAF:type()}, S) -> {boolean(), S} when T :: ?ATOM:type().
is_empty_line({[], [], _T}, ST) -> {false, ST};
is_empty_line({[], Neg, T}, ST) -> is_empty_line({[ty_map:any()], Neg, T}, ST);
is_empty_line({Pos, Neg, T}, ST) ->
  T = ?LEAF:any(), % sanity
  BigInt = ty_map:big_intersect(Pos),
  phi(ty_map:components(BigInt), [ty_map:components(N) || N <- Neg], ST).

-spec phi([T], [[T]], S) -> {boolean(), S} when T :: ty_tuple:type().
phi(P, [], ST0) ->
  PP = lists:filter(fun(Tp) -> {IsEmpty, _} = dnf_ty_tuple:phi(ty_tuple:components(Tp), [], ST0), not IsEmpty end, P),
  Keys = [begin [X, _] = ty_tuple:components(Tp), X end || Tp <- PP],
  KeyUnion = lists:foldr(fun ?NODE:union/2, ?NODE:empty(), Keys),
  {not ?NODE:is_empty(?NODE:negate(KeyUnion)), ST0};
phi(P, [N | Ns], ST0) ->
  InductiveCase = fun(Tp, {true, ST1}) -> dnf_ty_tuple:phi(ty_tuple:components(Tp), N, ST1);
                     (_Tp, {false, ST1}) -> {false, ST1}
                  end,
  case lists:foldr(InductiveCase, {true, ST0}, P) of
    {false, ST1} -> phi(P, Ns, ST1);
    {true, ST1} -> {true, ST1}
  end.

-spec normalize_line({[T], [T], ?LEAF:type()}, monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when T :: ?ATOM:type().
normalize_line({[], [], _T}, _Fixed, ST) -> {[], ST};
normalize_line({[], Neg, T}, Fixed, ST) -> normalize_line({[ty_map:any()], Neg, T}, Fixed, ST);
normalize_line({Pos, Neg, T}, Fixed, ST) ->
%%  io:format(user, "FIXED", []),
%%  io:format(user, "~n~p~n", [Fixed]),
%%  io:format(user, "POS MAPs", []),
%%  lists:foreach(fun(P) -> {Ty, _} = ty_map:unparse(P, ST), io:format(user, "~n~ts~n", [pretty:render_ty(Ty)]) end, Pos),
%%  io:format(user, "NEG MAPs", []),
%%  lists:foreach(fun(N) -> {Ty, _} = ty_map:unparse(N, ST), io:format(user, "~n~ts~n", [pretty:render_ty(Ty)]) end, Neg),
  T = ?LEAF:any(), % sanity
  BigInt = ty_map:big_intersect(Pos),
  phi_norm(ty_map:components(BigInt), [ty_map:components(N) || N <- Neg], Fixed, ST).

-spec phi_norm([T], [[T]], monomorphic_variables(), S) -> {set_of_constraint_sets(), S} when T :: ty_tuple:type().
phi_norm(P, [], _Fixed, ST0) ->
  case phi(P, [], ST0) of {true, ST1} -> {[[]], ST1}; {false, ST1} -> {[], ST1}  end;
%%  lists:foldr(
%%    fun(Tp, {Cs, ST1}) ->
%%      [_, Y] = ty_tuple:components(Tp),
%%      case etally:is_tally_satisfiable([{Y, ?NODE:empty()}], Fixed) of
%%        false -> {Cs, ST1};
%%        true ->
%%          Keys = [begin [X2, _] = ty_tuple:components(Tp2), X2 end || Tp2 <- P -- [Tp]],
%%          KeyUnion = lists:foldr(fun ?NODE:union/2, ?NODE:empty(), Keys),
%%          case etally:is_tally_satisfiable([{Y, ?NODE:empty()}, {?NODE:negate(KeyUnion), ?NODE:empty()}], Fixed) of
%%            true -> {Cs, ST1}; % #{K => K\1, -K => _}
%%            false ->
%%              {Cs2, ST2} = ty_node:normalize(Y, Fixed, ST1),
%%              {constraint_set:join(Cs2, Cs, Fixed), ST2}
%%          end
%%      end
%%    end, {[], ST0}, P);
phi_norm(P, [N | Ns], Fixed, ST0) ->
  {CSet1, ST1} = lists:foldr(
    fun(Tp, {Cs, ST1}) ->
      {Cs2, ST2} = dnf_ty_tuple:phi_norm(ty_tuple:components(Tp), N, Fixed, ST1),
      {constraint_set:meet(Cs2, Cs, Fixed), ST2}
    end,
    {[[]], ST0},
    P),
  {CSet2, ST2} = phi_norm(P, Ns, Fixed, ST1),
  {constraint_set:join(CSet1, CSet2, Fixed), ST2}.


-spec all_variables_line([T], [T], ?LEAF:type(), cache()) -> sets:set(variable()) when T :: ?ATOM:type().
all_variables_line(P, N, Leaf, Cache) ->
  Leaf = ty_bool:any(),
  sets:union(
    [ty_map:all_variables(M, Cache) || M <- P]
    ++ [ty_map:all_variables(M, Cache) || M <- N]
  ).
