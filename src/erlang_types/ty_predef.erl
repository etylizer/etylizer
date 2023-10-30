-module(ty_predef).

%% Predef representation


-export([compare/2, equal/2]).


-export([empty/0, any/0]).
-export([union/2, intersect/2, diff/2, negate/1, is_any/1]).
-export([is_empty/1, eval/1, normalize/5, substitute/4]).

-export([predef/1, transform/2, all_variables/1]).

substitute(_, Ty, _, _) ->  Ty.

all_variables(_) -> [].
predef(Predef) ->
    false = is_list(Predef),
    [Predef].

transform([], #{empty := E}) -> E();
transform(All = [Predef | Others], Ops = #{union := U, any := A}) ->
    AllS = lists:sort(All),
    case any() of
        AllS -> A();
        _ -> U([transform_single(Predef, Ops), transform(Others, Ops)])
    end.

transform_single(Predef, #{to_predef := P}) ->
    P(Predef).

% TODO witness
eval(_) -> erlang:error("TODO").

empty() -> [].
any() -> [ '[]', float, pid, port, reference ].

compare(X, Y) when X > Y -> 1;
compare(X, Y) when X < Y -> -1;
compare(_, _) -> 0.

equal(I1, I2) -> I1 =:= I2.

is_empty([]) -> true;
is_empty(_) -> false.

is_any(_) -> error(not_possible).

negate(All) -> any() -- All.

union(P1, P2) ->
    lists:usort(P1 ++ P2).

intersect(P1, P2) ->
    [X || X <- P1, lists:member(X, P2)].

diff(I1, I2) ->
    intersect(I1, negate(I2)).

normalize(TyPredef, [], [], _Fixed, _) ->
    % Fig. 3 Line 3
    case is_empty(TyPredef) of
        true -> [[]];
        false -> []
    end;
normalize(TyPredef, PVar, NVar, Fixed, M) ->
    Ty = ty_rec:predef(dnf_var_predef:predef(TyPredef)),
    % ntlv rule
    ty_variable:normalize(Ty, PVar, NVar, Fixed, fun(Var) -> ty_rec:predef(dnf_var_predef:var(Var)) end, M).