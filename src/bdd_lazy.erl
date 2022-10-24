-module(bdd_lazy).

-export([union/2, intersect/2, diff/2, negate/1]).
-export([eval/1]).
-export([substitute/3]).
-export([empty/0, any/0]).
-export([pos/1]).

-spec union    (bdd(), bdd()) -> bdd().
-spec intersect(bdd(), bdd()) -> bdd().
-spec diff     (bdd(), bdd()) -> bdd().

%% To ensure that the atoms occurring on a path are distinct, 
%% we define use the total order of Erlang atoms and impose
%% that on every path the order of the labels strictly increases.

-type bdd() :: {bdd, 0} | {bdd, 1} | {bdd, east:ty(), bdd(), bdd(), bdd()}.

-define(EMPTY, {bdd, 0}).
-define(ANY,   {bdd, 1}).
-define(NODE(A, BLeft, BMiddle, BRight), {bdd, A, BLeft, BMiddle, BRight}).

-define(CNODE(A, BLeft, BMiddle, BRight),
    case BMiddle of
        ?ANY -> ?ANY;
        _ ->
            case BLeft == BRight of
                true -> union(BLeft, BMiddle);
                _ -> {bdd, A, BLeft, BMiddle, BRight}
            end
    end
).

eval(?EMPTY) ->
    {predef, none};
eval(?ANY) ->
    {predef, any};
eval(?NODE(A, Left, Middle, Right)) ->
    {union, [
        {intersection, [eval(A), eval(Left)]},
        eval(Middle),
        {intersection, [{negation, eval(A)}, eval(Right)]}
    ]};
eval({bdd_spec, empty_list}) ->
    {empty_list};
eval({bdd_spec, T}) when T == float; T == reference; T == pid; T == port ->
    {predef, T};
eval({bdd_atom, A}) ->
    stdtypes:tatom(A);
eval({bdd_tuple, Components}) ->
    Args = [ty_rec:eval(X) || X <- Components],
    stdtypes:ttuple(Args);
eval({bdd_list, T, Term}) ->
    stdtypes:tlist_improper(ty_rec:eval(T), ty_rec:eval(Term));
eval({bdd_fun_full, A, B}) ->
    Args = [ty_rec:eval(X) || X <- A],
    {fun_full, Args, ty_rec:eval(B)};
eval({bdd_var, Var}) ->
    {var, Var};
eval({bdd_range, '*', '*'}) ->
    {predef, integer};
eval({bdd_range, From, To}) when is_integer(From), is_integer(To) ->
    {range, From, To};
eval(B) ->
    logger:warning("Unhandled ~p", [B]),
    throw(bdd_todo).

empty() -> ?EMPTY.
any() -> ?ANY.
pos(Ty) -> ?NODE(Ty, ?ANY, ?EMPTY, ?EMPTY).

% early pattern matching against trivial cases is necessary
% proper shows that trivial operations are not simplified
union(B, B) -> B;
union(?ANY, _B) -> ?ANY;
union(_B, ?ANY) -> ?ANY;
union(?EMPTY, B) -> B;
union(B, ?EMPTY) -> B;
union(_B1 = ?NODE(A1,C1,U1,D1), _B2 = ?NODE(A2,C2,U2,D2))  when A1 =:= A2 -> ?CNODE(A1, union(C1, C2), union(U1, U2), union(D1, D2));
union(_B1 = ?NODE(A1,C1,U1,D1), B2 = ?NODE(A2,_C2,_U2,_D2)) when A1  <  A2 -> ?CNODE(A1, C1, union(U1, B2), D1);
union(B1 = ?NODE(A1,_C1,_U1,_D1), _B2 = ?NODE(A2,C2,U2,D2)) when A1  >  A2 -> ?CNODE(A2, C2, union(B1, U2), D2).

intersect(B, B) -> B;
intersect(?ANY, B) -> B;
intersect(B, ?ANY) -> B;
intersect(?EMPTY, _B) -> ?EMPTY;
intersect(_B, ?EMPTY) -> ?EMPTY;
intersect(A, B) -> negate(union(negate(A), negate(B))).

diff(B, B) -> ?EMPTY;
diff(_B, ?ANY) -> ?EMPTY;
diff(?ANY, B) -> negate(B);
diff(B, ?EMPTY) -> B;
diff(?EMPTY, _B) -> ?EMPTY;
diff(A, B) -> intersect(A, negate(B)).


% FIXME debug dialyzer issue
-dialyzer({nowarn_function, negate/1}).
negate(?EMPTY) ->  ?ANY;
negate(?ANY) ->  ?EMPTY;
negate(?NODE(A, B1, B2, ?EMPTY)) -> ?CNODE(A, ?EMPTY, negate(union(B2, B1)), negate(B2));
negate(?NODE(A, ?EMPTY, B2, B3)) -> ?CNODE(A, negate(B2), negate(union(B2, B3)), ?EMPTY);
negate(?NODE(A, B1, ?EMPTY, B3)) -> ?CNODE(A, negate(B1), negate(union(B1, B3)), negate(B3));
negate(?NODE(A, B1, B2, B3)) -> ?CNODE(A, negate(union(B1, B2)), ?EMPTY, negate(union(B3, B2))).


substitute_atom(Mode, Var, Map) ->
    case maps:find({var, Var}, Map) of
        error ->
            bdd_lazy:pos({bdd_var, Var});
        {ok, Target} ->
            Norm = ty_rec:norm(Target),
            ty_rec:pi(Mode, Norm)
    end.

substitute(_Mode, B, _) when B == {bdd, 0}; B == {bdd, 1} -> B;
substitute(Mode, {bdd, {bdd_var, Var}, Left, Middle, Right}, Map) ->
    BddFromAtom = substitute_atom(Mode, Var, Map),

    NewLeft = intersect(BddFromAtom, substitute(Mode, Left, Map)),
    NewRight = intersect(BddFromAtom, substitute(Mode, Right, Map)),

    union(union(NewLeft, NewRight), substitute(Mode, Middle, Map));
substitute(Mode, {bdd, Atom, Left, Middle, Right}, Map) ->
    {bdd, substitute_rec(Atom, Map),
        substitute(Mode, Left, Map),
        substitute(Mode, Middle, Map),
        substitute(Mode, Right, Map)
    }.


substitute_rec(T = {bdd_atom, _}, _) -> T;
substitute_rec(T = {bdd_spec, _}, _) -> T;
substitute_rec(T = {bdd_range, _, _}, _) -> T;
substitute_rec({bdd_fun_full, Components, Return}, Map) ->
    {bdd_fun_full, lists:map(fun(C) -> ty_rec:substitute_bdd(Map, C) end, Components), ty_rec:substitute_bdd(Map, Return)};
substitute_rec({bdd_tuple, Components}, Map) ->
    {bdd_tuple, lists:map(fun(C) -> ty_rec:substitute_bdd(Map, C) end, Components)};
substitute_rec({bdd_list, Element, Termination}, Map) ->
    {bdd_list, ty_rec:substitute_bdd(Map, Element), ty_rec:substitute_bdd(Map, Termination) };
substitute_rec(Atom, _Map) ->
    logger:error("Subst! ~p", [Atom]),
    throw(todo_branch).