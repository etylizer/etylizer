
-module(stdtypes).

-include_lib("log.hrl").

% @doc Type1sfor funcions and operatortfun([Arg], Res).
-export([
    tspecial_any/0,
    tempty_list/0,
    tfloat/0,
    tint/0, tint/1,
    tbool/0,
    tlist_any/0,
    tlist_improper/2,
    tnonempty_improper_list/2,
    tlist/1,
    tnonempty_list/0,
    tnonempty_list/1,
    builtin_ops/0, builtin_funs/0,
    tatom/0, tatom/1,
    tintersect/1, tunion/1, tunion/2, tnegate/1,
    tinter/1, tinter/2,
    tyscm/2,
    any/0,
    empty/0,
    ttuple/1, ttuple_n/1, ttuple_any/0, ttuple1/1, ttuple2/2,
    tarrow_n/1,
    tfun_full/2,
    tfun/2, tfun1/2, tfun2/3, tfun_any/0,
    tmap/1, tmap/2, tmap_field_opt/2, tmap_field_man/2, tmap_any/0,
    tvar/1,
    trange_any/0, trange/2,
    expand_predef_alias/1,
    tany/0,
    tnone/0,
    tnot/1,
    tmu/2,
    is_tlist/1,
    init/0, cleanup/0
]).

-include_lib("parse.hrl").

%% Builtin types


is_tlist({improper_list, _, _}) -> true;
is_tlist({negation, {improper_list, _, _}}) -> true;
is_tlist(_) -> false.

tmu(_,_) -> throw(todo_mu).

-spec tinter([ast:ty()]) -> ast:ty().
tinter(Tys) -> {intersection, Tys}.

-spec tinter(ast:ty(), ast:ty()) -> ast:ty().
tinter(T1, T2) -> tinter([T1, T2]).

-spec tfun([ast:ty()], ast:ty()) -> ast:ty().
tfun(Args, Res) -> {fun_full, Args, Res}.

-spec tfun1(ast:ty(), ast:ty()) -> ast:ty().
tfun1(Arg, Res) -> tfun([Arg], Res).

-spec tfun2(ast:ty(), ast:ty(), ast:ty()) -> ast:ty().
tfun2(Arg1, Arg2, Res) -> tfun([Arg1, Arg2], Res).

-spec tatom() -> ast:ty().
tatom() -> {predef, atom}.

-spec tatom(atom()) -> ast:ty().
tatom(A) -> {singleton, A}.

-spec tint() -> ast:ty().
tint() -> {predef, integer}.

-spec tint(integer()) -> ast:ty().
tint(A) -> {singleton, A}.

-spec tfloat() -> ast:ty().
tfloat() -> {predef, float}.

-spec tlist(ast:ty()) -> ast:ty().
tlist(Arg) -> {list, Arg}.

-spec tmap([ast:ty_map_assoc()]) -> ast:ty().
tmap(AssocList) -> {map, AssocList}.

-spec tmap(ast:ty(), ast:ty()) -> ast:ty().
tmap(T1, T2) -> {map, [tmap_field_opt(T1, T2)]}.

-spec tmap_field_opt(ast:ty(), ast:ty()) -> ast:ty_map_assoc_opt().
tmap_field_opt(K, V) -> {map_field_opt, K, V}.

-spec tmap_field_man(ast:ty(), ast:ty()) -> ast:ty_map_assoc_req().
tmap_field_man(K, V) -> {map_field_req, K, V}.

-spec ttuple_n(pos_integer()) -> ast:ty().
ttuple_n(Size) ->
    {tuple, [{predef, any} || _ <- lists:seq(1, Size)]}.

tarrow_n(Size) ->
    {fun_full, [{predef, none} || _ <- lists:seq(1, Size)], {predef, any}}.

tfun_full(Args, Result) ->
    {fun_full, Args, Result}.

ttuple(Components) ->
    {tuple, Components}.

ttuple1(T) ->
    {tuple, [T]}.

ttuple2(T, U) ->
    {tuple, [T, U]}.

tintersect(Components) ->
    {intersection, Components}.

tnegate(Ty) ->
    {negation, Ty}.

tnot(Ty) -> tnegate(Ty).

tunion(Components) ->
    {union, Components}.

tunion(A, B) -> tunion([A, B]).

any() ->
    {predef, any}.

empty() ->
    {predef, none}.

tany() ->
    {predef, any}.

tnone() ->
    {predef, none}.

ttuple_any() ->
    {tuple_any}.

tfun_any() ->
    {fun_simple}.

tmap_any() ->
    {map_any}.

trange_any() ->
    {predef, integer}.

trange(From, To) ->
    {range, From, To}.

%% Builtin type aliases

tspecial_any() ->
    tunion([
        {empty_list},
        {predef, float},
        {predef, pid},
        {predef, port},
        {predef, reference}
    ]).

tlist_any() ->
    {improper_list, {predef, any}, {predef, any}}.

tlist_improper(A, B) ->
    {improper_list, A, B}.

-spec tnonempty_improper_list(ast:ty(), ast:ty()) -> ast:ty().
tnonempty_improper_list(A, B) ->
    {nonempty_improper_list, A, B}.

tempty_list() -> {empty_list}.

-spec tnonempty_list(ast:ty()) -> ast:ty().
tnonempty_list(Arg) -> {nonempty_list, Arg}.

-spec tnonempty_list() -> ast:ty().
tnonempty_list() -> {predef_alias, nonempty_list}.

-spec tbool() -> ast:ty().
tbool() -> {predef_alias, boolean}.

-spec expand_predef_alias(ast:predef_alias_name()) -> ast:ty().
expand_predef_alias(term) -> {predef, any};
expand_predef_alias(binary) -> throw(todo); %% TODO
expand_predef_alias(nonempty_binary) -> throw(todo); %% TODO
expand_predef_alias(bitstring) -> throw(todo); %% TODO
expand_predef_alias(nonempty_bitstring) -> throw(todo); %% TODO
expand_predef_alias(boolean) -> {union, [{singleton, true}, {singleton, false}]};
expand_predef_alias(byte) -> {range, 0, 255};
expand_predef_alias(char) -> {range, 0, 1114111};
expand_predef_alias(nil) -> {empty_list};
expand_predef_alias(number) -> {union, [{predef, float}, {predef, integer}]};
expand_predef_alias(list) -> {list, {predef, any}};
expand_predef_alias(nonempty_list) -> {nonempty_list, {predef, any}};
expand_predef_alias(maybe_improper_list) -> errors:not_implemented("expand maybe_improper_list");
expand_predef_alias(nonempty_improper_list) -> {nonempty_improper_list, {predef, any}, {predef, any}};
expand_predef_alias(nonempty_maybe_improper_list) -> throw(error_todo); %% TODO what is a maybe improper list vs improper list?
expand_predef_alias(string) -> {list, expand_predef_alias(char)};
expand_predef_alias(nonempty_string) -> {nonempty_list, expand_predef_alias(char)};
%% iodata and iolist are recursively defined and are expanded in the
%% subtype relation into a recursive type
expand_predef_alias(iodata) -> throw(rec_type_not_supported_outside_esubrel);
expand_predef_alias(iolist) -> throw(rec_type_not_supported_outside_esubrel);
expand_predef_alias(map) -> {map, [{map_field_opt, {predef, any}, {predef, any}}]};
expand_predef_alias(function) -> {fun_simple};
expand_predef_alias(module) -> tatom();
expand_predef_alias(mfa) -> {tuple, [tatom(), tatom(), {predef, integer}]};
expand_predef_alias(arity) -> {predef, integer};
expand_predef_alias(identifier) -> {union, [{predef, pid}, {predef, port}, {predef, reference}]};
expand_predef_alias(node) -> tatom();
expand_predef_alias(timeout) -> {union, [{singleton, infinity}, expand_predef_alias(non_neg_integer)]};
expand_predef_alias(no_return) -> {predef, none};
expand_predef_alias(non_neg_integer) -> {range, 0, '*'};
expand_predef_alias(pos_integer) -> {range, 1, '*'};
expand_predef_alias(neg_integer) -> {range, '*', -1};

expand_predef_alias(Name) ->
    logger:error("Not expanding: ~p", [Name]),
     errors:not_implemented("expand_predef_alias").

%% Other types

-spec tvar(atom()) -> ast:ty().
tvar(T) -> {var, T}.

-spec tyscm(ast:ty()) -> ast:ty_scheme().
tyscm(Ty) -> {ty_scheme, [], Ty}.

-spec tyscm([atom()], ast:ty()) -> ast:ty_scheme().
tyscm(Vars, Ty) -> {ty_scheme, lists:map(fun(Alpha) -> {Alpha, {predef, any}} end, Vars), Ty}.

%% Types for builtin operations

-spec builtin_ops() -> [{atom(), arity(), ast:ty_scheme()}].
builtin_ops() ->
    NumOpTy = tyscm(tinter([
        tfun([tint(), tint()], tint()),
        tfun([tint(), tfloat()], tfloat()),
        tfun([tfloat(), tint()], tfloat()),
        tfun([tfloat(), tfloat()], tfloat())
    ])),
    NumOp1Ty = tyscm(tinter([
        tfun([tint()], tint()),
        tfun([tfloat()], tfloat())
    ])),
    IntOpTy = tyscm(tfun([tint(), tint()], tint())),
    BoolOpTy = tyscm(tfun([tbool(), tbool()], tbool())),
    BoolShortcutOpTy = tyscm(tfun([tbool(), tvar(a)], tvar(a))),
    PolyOpTy = tyscm(tfun([tvar(a), tvar(a)], tbool())),
    [
        {'+', 2, NumOpTy},
        {'-', 2, NumOpTy},
        {'-', 1, NumOp1Ty},
        {'*', 2, NumOpTy},
        {'/', 2, tyscm(tinter([
            tfun([tint(), tint()], tfloat()),
            tfun([tint(), tfloat()], tfloat()),
            tfun([tfloat(), tint()], tfloat()),
            tfun([tfloat(), tfloat()], tfloat())]))},
        {'div', 2, IntOpTy},
        {'rem', 2, IntOpTy},
        {'band', 2, IntOpTy},
        {'bor', 2, IntOpTy},
        {'bxor', 2, IntOpTy},
        {'bsl', 2, IntOpTy},
        {'bsr', 2, IntOpTy},
        {'not', 1, tyscm(tfun([tbool()], tbool()))},
        {'and', 2, BoolOpTy},
        {'or', 2, BoolOpTy},
        {'xor', 2, BoolOpTy},
        {'orelse', 2, BoolShortcutOpTy},
        {'andalso', 2, BoolShortcutOpTy},
        {'==', 2, PolyOpTy},
        {'/=', 2, PolyOpTy},
        {'=<', 2, PolyOpTy},
        {'<', 2, PolyOpTy},
        {'>=', 2, PolyOpTy},
        {'>', 2, PolyOpTy},
        {'=:=', 2, PolyOpTy},
        {'=/=', 2, PolyOpTy},
        {'++', 2, tyscm([a], tfun([tlist(tvar(a)), tlist(tvar(a))], tlist(tvar(a))))},
        {'--', 2, tyscm([a], tfun([tlist(tvar(a)), tlist(tvar(a))], tlist(tvar(a))))}
        % {'!', 2,   FIXME
    ].

%% Types for builtin functions

-type fun_types() :: [{atom(), arity(), ast:ty_scheme()}].

-spec extra_funs() -> fun_types().
extra_funs() ->
    [{record_info, 2, tyscm(tinter([tfun([tatom(fields), tatom()], tlist(tatom())),
                                    tfun([tatom(size), tatom()], tint())]))}].

-define(TABLE, stdtypes_table).

-spec init() -> ok.
init() ->
    case ets:whereis(?TABLE) of
        undefined -> ok;
        _ -> cleanup()
    end,
    ets:new(?TABLE, [set, named_table, {keypos, 1}]),
    ok.

-spec cleanup() -> ok.
cleanup() ->
    ets:delete(?TABLE),
    ok.

-spec builtin_funs() -> fun_types().
builtin_funs() ->
    Key = stdtypes,
    case ets:whereis(?TABLE) of
        undefined -> init();
        _ -> ok
    end,
    Dir = utils:assert_no_error(code:lib_dir(erts)),
    Path = filename:join([Dir, "src", "erlang.erl"]),
    Hash = utils:hash_file(Path),
    case ets:lookup(?TABLE, Key) of
        [{_, {StoredHash, Result}}] when Hash =:= StoredHash -> Result;
        [] ->
            X = mk_builtin_funs(Path),
            true = ets:insert(?TABLE, {Key, {Hash, X}}),
            X;
        Y -> ?ABORT("Unexpected entry in stdtypes_table: ~p", Y)
    end.

-spec mk_builtin_funs(file:filename()) -> fun_types().
mk_builtin_funs(Path) ->
    ?LOG_DEBUG("Creating types for builtin functions"),
    RawForms = parse:parse_file_or_die(Path, #parse_opts{
                                                verbose = false
                                               }),
    {Exports, RawSpecs} =
        lists:foldl(
          fun (Form, Acc = {Exports, Specs}) ->
                  case Form of
                      {attribute, _, export, Funs} ->
                          {utils:set_add_many(Funs, Exports), Specs};
                      {attribute, _, spec, _} ->
                          {Exports, [Form | Specs]};
                      _ -> Acc
                  end
          end,
          {sets:new(), []}, RawForms),
    AllSpecs = ast_transform:trans(Path, lists:reverse(RawSpecs), flat, varenv:empty("function")),
    Result =
        lists:filtermap(
          fun (Spec) ->
                  case Spec of
                      {attribute, _, spec, Name, Arity, Ty, without_mod} ->
                          case sets:is_element({Name, Arity}, Exports) of
                              true -> {true, {Name, Arity, Ty}};
                              false -> false
                          end;
                      _ -> false
                  end
          end, AllSpecs) ++ extra_funs(),
    ?LOG_TRACE2("Builtin functions: ~200p", Result),
    Result.
