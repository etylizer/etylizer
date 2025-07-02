-module(ty_tuple).

-export([
  compare/2,
  equal/2,
  tuple/1,
  any/1,
  empty/1,
  all_variables/2,
  unparse/2,
  big_intersect/1,
  components/1
]).

-ifndef(NODE).
-define(NODE, ty_node).
-endif.
%% n-tuple representation



compare(A, B) when A < B -> lt;
compare(A, B) when A > B -> gt;
compare(_, _) -> eq.

equal(P1, P2) -> compare(P1, P2) =:= eq.

tuple(Refs) -> {ty_tuple, length(Refs), Refs}.

empty(Size) -> {ty_tuple, Size, [?NODE:empty() || _ <- lists:seq(1, Size)]}.
any(Size) -> {ty_tuple, Size, [?NODE:any() || _ <- lists:seq(1, Size)]}.


components({ty_tuple, _, Refs}) -> Refs.
pi(I, {ty_tuple, _, Refs}) -> lists:nth(I, Refs).

big_intersect([]) -> error(illegal_state);
big_intersect([X]) -> X;
big_intersect([X | Y]) ->
    lists:foldl(fun({ty_tuple, _, Refs}, {ty_tuple, Dim, Refs2}) ->
        true = length(Refs) == length(Refs2),
        {ty_tuple, Dim, [?NODE:intersect(S, T) || {S, T} <- lists:zip(Refs, Refs2)]}
                end, X, Y).


all_variables({ty_tuple, _, Refs}, Cache) ->
  sets:union(
    [ty_node:all_variables(T, Cache) || T <- Refs]
  ).

unparse({ty_tuple, _, Refs}, ST0) ->
  {All, ST3} = lists:foldl(
                 fun(R, {Cs, ST1}) -> {C, ST2} = ty_node:unparse(R, ST1), {Cs ++ [C], ST2} end, 
                 {[], ST0}, 
                 Refs
                ),
  {{tuple, All}, ST3}.

% -ifdef(TEST).
% -include_lib("eunit/include/eunit.hrl").

% usage_test() ->
%     % (int, int)
%     TIa = ty_rec:interval(dnf_var_ty_interval:int(dnf_ty_interval:interval('*', '*'))),
%     TIb = ty_rec:interval(dnf_var_ty_interval:int(dnf_ty_interval:interval('*', '*'))),

%     _Ty_Tuple = ty_tuple:tuple([TIa, TIb]),

%     ok.

% -endif.
