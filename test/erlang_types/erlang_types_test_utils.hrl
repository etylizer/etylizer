-define(LOAD, begin [code:ensure_loaded(M) || M <- [
    persistent_term, constraint_set, dnf_ty_atom, dnf_ty_bitstring,
    dnf_ty_function, dnf_ty_interval, dnf_ty_list, dnf_ty_map, dnf_ty_predefined,
    dnf_ty_tuple, dnf_ty_variable, global_state, ty_bool, ty_function, ty_functions, 
    ty_node, ty_parser, ty_rec, ty_tuple, ty_tuples, ty_variable,
    ty, tarjan, utils
  ]]end).

-compile([nowarn_export_all, export_all]).

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
tint(A) -> {range, A, A}.
tint(A,B) -> {range, A, B}.
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
test_key(Key) -> test_key(Key, 0).
test_key(Key, LenArgs) -> {test_key, '.', Key, LenArgs}.
tnamed_ns(Ns, Ref, Args) -> 
  {named, {loc, "AUTO", -1, -1}, {ty_ref, Ns, Ref, length(Args)}, Args}.
tnamed(Ref) -> tnamed(Ref, []).
tnamed(Ref, Args) ->
  % Use the dummy '.' file as the module for testing purposes
  tnamed_ns('.', Ref, Args).

tyscm(Ty) -> {ty_scheme, [], Ty}.
tyscm(Vars, Ty) -> {ty_scheme, lists:map(fun(Alpha) -> {Alpha, {predef, any}} end, Vars), Ty}.
tmu(Var, Ty) -> {mu, Var, Ty}.
tmap_any() -> {map_any}.
tmap(Fields) -> {map, Fields}.
tmap_field_req(K, V) -> {map_field_req, K, V}.
tmap_field_opt(K, V) -> {map_field_opt, K, V}.

with_symtab(Fun, Definitions) when is_map(Definitions) -> % map
  with_symtab(Fun, maps:to_list(Definitions));
with_symtab(Fun, Definitions) when is_list(Definitions) -> % list
  global_state:with_new_state(fun() ->
    lists:foreach(fun({Key, Scheme}) -> 
      ty_parser:extend_symtab(Key, Scheme) 
    end, Definitions),
    Fun()
  end);
with_symtab(Fun, SymTab) -> % full symtab
  global_state:with_new_state(fun() ->
    Types = symtab:get_types(SymTab),
    maps:foreach(fun(K, V) -> ty_parser:extend_symtab(K, V) end, Types),
    Fun()
  end).

with_type(Fun, {Type, Types}) when is_map(Types) ->
  global_state:with_new_state(fun() ->
    % load all nodes directly, assume no collisions
    maps:foreach(fun(Node, Descriptor) -> 
      ty_node:force_load(Node, Descriptor)
    end, Types),
    Fun(Type)
  end);
with_type(Fun, Types) ->
  global_state:with_new_state(fun() ->
    % load all nodes directly, assume no collisions
    maps:foreach(fun(Node, Descriptor) -> 
      ty_node:force_load(Node, Descriptor)
    end, Types),
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

system(File) ->
  {ok, [System]} = file:consult(File),
  System.

