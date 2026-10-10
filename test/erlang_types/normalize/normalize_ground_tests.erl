-module(normalize_ground_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

% Normalization hands types without polymorphic variables over to the subtype check:
% ty_node:normalize/3 for a whole type, dnf_ty_tuple:normalize_line/3 and
% dnf_ty_function:normalize_line/3 for a line of a type that has variables elsewhere.
% Walking the ground inclusions below takes time exponential in ?N instead,
% so without the hand-over these tests run into the timeout of eunit.
-define(N, 16).

tag(Prefix, I) -> b(list_to_atom(Prefix ++ integer_to_list(I))).

% {tI, integer()}
rec(I) -> ttuple([tag("t", I), tint()]).

% [{t0, integer()}] and [{t0, integer()}] | ... | [{tN, integer()}]
list0() -> tlist(rec(0)).
lists() -> u([tlist(rec(I)) || I <- lists:seq(0, ?N)]).

% the same as recursive tuple types: mu X . nil | {{tI, integer()}, X}
chain(I) -> tmu(tvar_mu(x), u(b(nil), ttuple([rec(I), tvar_mu(x)]))).
chain0() -> chain(0).
chains() -> u([chain(I) || I <- lists:seq(0, ?N)]).

% ({{t0}} -> r0) & ({{t1}} -> not c1) & ... & ({{tN}} -> not cN) and {{t0}} -> r0 | rx
box(I) -> ttuple([ttuple([tag("t", I)])]).
arrows() -> i([a(box(0), b(r0)) | [a(box(I), n(tag("c", I))) || I <- lists:seq(1, ?N)]]).
arrow0() -> a(box(0), u(b(r0), b(rx))).

% normalize S \ T and apply the continuation to the result while the type state is alive
normalize(S, T, Fixed, Check) ->
  global_state:with_new_state(fun() ->
    Mono = maps:from_list([{ty_variable:new_with_name(Var), []} || Var <- Fixed]),
    Check(ty_node:normalize(ty_node:difference(ty_parser:parse(S), ty_parser:parse(T)), Mono))
  end).

sat(S, T) -> sat(S, T, []).
sat(S, T, Fixed) -> normalize(S, T, Fixed, fun(Res) -> [[]] = Res, ok end).

unsat(S, T) -> unsat(S, T, []).
unsat(S, T, Fixed) -> normalize(S, T, Fixed, fun(Res) -> [] = Res, ok end).

% a single constraint Lower <= Var <= Upper
bounds(S, T, Fixed, {Var, Lower, Upper}) ->
  normalize(S, T, Fixed, fun(Res) ->
    V = ty_variable:new_with_name(Var),
    [[{V, L, U}]] = Res,
    true = ty_node:leq(L, ty_parser:parse(Lower)) andalso ty_node:leq(ty_parser:parse(Lower), L),
    true = ty_node:leq(U, ty_parser:parse(Upper)) andalso ty_node:leq(ty_parser:parse(Upper), U),
    ok
  end).

ground_list_test() ->
  sat(list0(), lists()),
  unsat(lists(), list0()).

ground_tuple_test() ->
  sat(chain0(), chains()),
  unsat(chains(), chain0()),
  sat(ttuple([tint(), list0()]), ttuple([tint(), lists()])),
  unsat(ttuple([tint(), lists()]), ttuple([tint(), list0()])).

ground_function_test() ->
  sat(arrows(), arrow0()),
  unsat(arrow0(), arrows()),
  sat(a(tint(), list0()), a(tint(), lists())),
  unsat(a(tint(), lists()), a(tint(), list0())),
  sat(a(tint(), chain0()), a(tint(), chains())),
  sat(a(chains(), tint()), a(chain0(), tint())).

% the tuple and the function are not ground, their components are
ground_component_test() ->
  bounds(ttuple([v(alpha), list0()]), ttuple([tint(), lists()]), [], {alpha, tnone(), tint()}),
  bounds(a(v(alpha), list0()), a(tint(), lists()), [], {alpha, tint(), tany()}),
  bounds(a(v(alpha), chain0()), a(tint(), chains()), [], {alpha, tint(), tany()}).

% the types are not ground, their list, tuple and function lines are
ground_line_test() ->
  Alpha = ttuple([v(alpha)]),
  Int = ttuple([tint()]),
  bounds(u(list0(), Alpha), u(lists(), Int), [], {alpha, tnone(), tint()}),
  bounds(u(chain0(), Alpha), u(chains(), Int), [], {alpha, tnone(), tint()}),
  bounds(u(arrows(), Alpha), u(arrow0(), Int), [], {alpha, tnone(), tint()}),
  unsat(u(lists(), Alpha), u(list0(), Int)),
  unsat(u(arrow0(), Alpha), u(arrows(), Int)).

% monomorphic variables are ground
monomorphic_variable_test() ->
  unsat(v(alpha), tint(), [alpha]),
  unsat(tint(), v(alpha), [alpha]),
  sat(i(v(alpha), tint()), tint(), [alpha]),
  sat(ttuple([v(alpha), list0()]), ttuple([v(alpha), lists()]), [alpha]),
  unsat(ttuple([v(alpha), list0()]), ttuple([v(beta), lists()]), [alpha, beta]),
  sat(a(v(alpha), list0()), a(v(alpha), lists()), [alpha]),
  % alpha is monomorphic, beta is not
  bounds(ttuple([v(alpha), list0()]), ttuple([v(beta), lists()]), [alpha], {beta, v(alpha), tany()}),
  bounds(u(list0(), ttuple([v(alpha)])), u(lists(), ttuple([v(beta)])), [alpha], {beta, v(alpha), tany()}).
