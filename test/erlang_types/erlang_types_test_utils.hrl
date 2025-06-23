a(A, B) -> {fun_full, [A], B}.
f() -> {fun_simple}.
f(A, B) -> {fun_full, A, B}.
b(A) -> {singleton, A}.
b() -> {predef, atom}.
tatom(A) -> {singleton, A}.
tatom() -> {predef, atom}.
n(S) -> {negation, S}.
u(A,B) -> {union, [A, B]}.
u(S) -> {union, S}.
i(A,B) -> {intersection, [A, B]}.
i(S) -> {intersection, S}.
tint() -> {range, '*', '*'}.
int() -> {range, '*', '*'}.
int(A) -> {range, A, A}.
tint(A) -> {range, A, A}.
int(A,B) -> {range, A, B}.
v(A) -> {var, A}.
tvar_mu(A) -> {mu_var, A}.
tempty() -> {predef, none}.
tbool() -> u(b(true), b(false)).
tnone() -> {predef, none}.
tany() -> {predef, any}.
tempty_list() -> {empty_list}.
tlist(T) -> {list, T}.
timproper_list(H, T) -> {improper_list, H, T}.
tnonempty_list(T) -> {nonempty_list, T}.
tnonempty_list() -> {predef_alias, nonempty_list}.
tnonempty_improper_list(H, T) -> {nonempty_improper_list, H, T}.
tfloat() -> {predef, float}.
p(A, B) -> {tuple, [A, B]}.
p(A) when not is_list(A) -> {tuple, [A]};
p(A) when is_list(A) -> {tuple, A}.
tbitstring() -> {bitstring}.
ttuple_any() -> {tuple_any}.
ttuple(Types) -> {tuple, Types}.
ttuple1(Type) -> {tuple, [Type]}.
tnamed(Ref) -> tnamed(Ref, []).
tnamed(Ref, Args) ->
  % Use the dummy '.' file as the module for testing purposes
  {named, {loc, "AUTO", -1, -1}, {ty_ref, '.', Ref, length(Args)}, Args}.
tyscm(Ty) -> {ty_scheme, [], Ty}.
tyscm(Vars, Ty) -> {ty_scheme, lists:map(fun(Alpha) -> {Alpha, {predef, any}} end, Vars), Ty}.
tmu(Var, Ty) -> {mu, Var, Ty}.
tmap_any() -> {map_any}.
tmap(Fields) -> {map, Fields}.
tmap_field_req(K, V) -> {map_field_req, K, V}.
tmap_field_opt(K, V) -> {map_field_opt, K, V}.

with_symtab(Fun, Definitions) when is_map(Definitions) ->
  with_symtab(Fun, maps:to_list(Definitions));
with_symtab(Fun, Definitions) when is_list(Definitions) ->
  global_state:with_new_state(fun() ->
    lists:foreach(fun({Key, Scheme}) -> 
      ty_parser:extend_symtab(Key, Scheme) 
    end, Definitions),
    Fun()
  end).


is_equiv(A, B) -> is_subtype(A, B) andalso is_subtype(B, A).

is_subtype(S, T) ->
  global_state:with_new_state(fun() ->
    {A, B} = {ty_parser:parse(S), ty_parser:parse(T)},
    % io:format(user,"A: ~p~n~p~n", [A, ty_node:dump(A)]),
    % io:format(user,"B: ~p~n~p~n", [B, ty_node:dump(B)]),
    ty_node:leq(A, B)
  end).

% state has to be initialized already to use this
is_subtype_stateful(S, T) ->
  {A, B} = {ty_parser:parse(S), ty_parser:parse(T)},
  ty_node:leq(A, B).

