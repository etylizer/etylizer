-module(ast).

% @doc This header file defines type specifications for our internal AST. It is
% heavily derived from the erlang ast (defined in ast_erl.erl). See the README for
% a description of the properties of the internal AST.

-export([setup_ets/0, ast_to_erlang_ty/1, erlang_ty_to_ast/1, ast_to_erlang_ty_var/1]).
-on_load(setup_ets/0).
-define(VAR_ETS, ast_norm_var_memo). % remember variable name -> variable ID to convert variables properly


% generated via
% grep -o '^-type [a-zA-Z_0-9]*' src/ast.erl | sed 's/-type //g' | grep -v '^gen_' | grep -v '^list[0-9]' | sed 's/^/    /g; s|$|/0,|g'
-export_type([
    global_ref/0,
    ty_varname/0,
    local_ref/0,
    any_ref/0,
    local_bind/0,
    local_ref_bind/0,
    loc/0,
    fun_with_arity/0,
    export_form/0,
    export_type_form/0,
    import_form/0,
    mod_form/0,
    fun_decl/0,
    fun_spec/0,
    record_decl/0,
    record_field/0,
    type_decl/0,
    form/0,
    forms/0,
    rep_atom/0,
    rep_char/0,
    rep_float/0,
    rep_integer/0,
    rep_string/0,
    atomic_lit/0,
    pat_bitstring/0,
    pat_bitstring_elem/0,
    pat_compound/0,
    pat_cons/0,
    pat_map/0,
    pat_nil/0,
    pat_record_fld_idx/0,
    pat_record/0,
    pat_tuple/0,
    pat_wildcard/0,
    pat_var/0,
    pat/0,
    exp_bitstring_compr/0,
    exp_bitstring_constr/0,
    exp_bitstring_elem/0,
    exp_block/0,
    exp_case/0,
    exp_catch/0,
    exp_cons/0,
    exp_fun_ref/0,
    exp_fun/0,
    exp_funcall/0,
    exp_if/0,
    exp_list_compr/0,
    exp_map_create/0,
    exp_map_update/0,
    exp_nil/0,
    exp_binop/0,
    exp_unop/0,
    exp_recv/0,
    exp_recv_after/0,
    exp_record_create/0,
    exp_record_access/0,
    exp_record_index/0,
    exp_record_update/0,
    exp_tuple/0,
    exp_try/0,
    exp_var/0,
    exp/0,
    exps/0,
    qual_gen/0,
    qual_bitstring_gen/0,
    qualifier/0,
    bitstring_tyspec/0,
    bitstring_tyspec_list/0,
    map_assoc_opt/0,
    map_assoc_req/0,
    map_assoc/0,
    binop/0,
    unop/0,
    case_clause/0,
    catch_clause/0,
    fun_clause/0,
    if_clause/0,
    guard/0,
    guard_test_bitstring_constr/0,
    guard_test_cons/0,
    guard_test_funcall/0,
    guard_test_map_create/0,
    guard_test_map_update/0,
    guard_test_nil/0,
    guard_test_binop/0,
    guard_test_unop/0,
    guard_test_record_create/0,
    guard_test_record_access/0,
    guard_test_record_index/0,
    guard_test_tuple/0,
    guard_test_var/0,
    guard_test/0,
    ty_singleton/0,
    ty_bitstring/0,
    ty_empty_list/0,
    ty_list/0,
    ty_simple_fun/0,
    ty_any_arg_fun/0,
    ty_full_fun/0,
    ty_fun/0,
    ty_integer_range/0,
    ty_map_any/0,
    ty_map/0,
    ty_map_assoc_opt/0,
    ty_map_assoc_req/0,
    ty_map_assoc/0,
    ty_predef/0,
    ty_record/0,
    ty_field/0,
    ty_named/0,
    ty_tuple_any/0,
    ty_tuple/0,
    ty_var/0,
    ty_union/0,
    ty_intersection/0,
    ty_negation/0,
    ty/0,
    ty_scheme/0,
    tydef/0,
    ty_constraint/0,
    unique_tok/0,
    local_varname/0
]).

-export([
    format_loc/1, to_loc/2, loc_auto/0, is_predef_name/1, is_predef_alias_name/1,
    local_varname_from_any_ref/1,
    mk_intersection/1, mk_union/1, mk_negation/1
]).

% General
-type global_ref() :: {ref, atom(), arity()} | {qref, atom(), atom(), arity()}.
-type ty_varname() :: atom().
-type unique_tok() :: integer().
-type local_varname() :: {atom(), unique_tok()}.
-type local_ref() :: {local_ref, local_varname()}. % refer to an existing local variable
-type any_ref() :: global_ref() | local_ref().
-type local_bind() :: {local_bind, local_varname()}. % bind a new local variable
-type local_ref_bind() :: local_ref() | local_bind().
-type loc() :: {loc, string(), integer(), integer()}. % file, line, column

-spec setup_ets() -> ok.
setup_ets() -> spawn(fun() -> catch(begin ets:new(?VAR_ETS, [public, named_table]), receive _ -> ok end end) end), ok.

-spec format_loc(loc()) -> string().
format_loc({loc, "AUTO", -1, -1}) -> "auto";
format_loc({loc, Path, Line, Col}) -> utils:sformat("~s:~w:~w", [Path, Line, Col]).

-spec to_loc(string(), ast_erl:anno()) -> loc().
to_loc(Path, Anno) ->
    Line = utils:with_default(erl_anno:line(Anno), -1),
    Col = utils:with_default(erl_anno:column(Anno), -1),
    {loc, Path, Line, Col}.

-spec loc_auto() -> loc().
loc_auto() -> {loc, "AUTO", -1, -1}.

-spec local_varname_from_any_ref(any_ref()) -> {true, local_varname()} | false.
local_varname_from_any_ref(Ref) ->
    case Ref of
        {local_ref, V} -> {true, V};
        _ -> false
    end.

% 8.1  Module Declarations and Forms
-type fun_with_arity() :: {atom(), arity()}.
-type ty_with_arity() :: {atom(), arity()}.
-type export_form() :: {attribute, loc(), export, [fun_with_arity()]}.
-type export_type_form() :: {attribute, loc(), export_type, [ty_with_arity()]}.
-type import_form() :: {attribute, loc(), import, {Mod::atom(),[fun_with_arity()]}}.
-type mod_form() :: {attribute, loc(), module, Mod::atom()}.
-type fun_decl() :: {function, loc(), Name::atom(), Arity::arity(), [fun_clause()]}.
-type fun_spec() :: {attribute, loc(), spec | callback, Name::atom(), Arity::arity(),
                     ty_scheme(),
                     % wether the spec was written with an explicit module name or not
                     without_mod | with_mod
                    }.
-type record_decl() :: {attribute, loc(), record, {Name::atom(), [record_field()]}}.
-type record_field() :: {record_field, loc(), atom(), untyped | ty(), no_default | exp()}.
-type type_decl() :: {attribute, loc(), type, transparent|opaque, tydef()}.

% The forall-quantified tyvars are bound in Rhs, Rhs contains no other type variables.
-type tydef() :: {Name::atom(), Rhs::ty_scheme()}.

% Attribute "-file(File,Line)" ignored.
% Wild attributes ignored.
-type form() :: export_form() | export_type_form() | import_form() | mod_form() | fun_decl()
    | fun_spec() | record_decl() | type_decl().
-type forms() :: [form()].

% 8.2  Atomic Literals
-type rep_atom() :: {'atom', loc(), atom()}.
-type rep_char() :: {'char', loc(), char()}.
-type rep_float() :: {'float', loc(), float()}.
-type rep_integer() :: {'integer', loc(), integer()}.
-type rep_string() :: {'string', loc(), [char()]}.
-type atomic_lit() :: rep_atom() | rep_char() | rep_float() | rep_integer() | rep_string().

% 8.3  Patterns

-type pat_bitstring() :: {bin, loc(), [pat_bitstring_elem()]}.
-type pat_bitstring_elem() :: gen_bitstring_elem(pat(), exp()).
-type pat_compound() :: {match, loc(), pat(), pat()}. %  P_1 = P_2
-type pat_nil() :: {nil, loc()}.
-type pat_cons() :: {cons, loc(), pat(), pat()}.
-type pat_op() :: {op, loc(), atom(), [pat()]}.
-type pat_map() :: {map, loc(), [pat_map_assoc()]}. %  #{A_1, ..., A_k} with Ai: P_i_1 := P_i_2
-type pat_map_assoc() :: {map_field_exact, loc(), pat(), pat()}.
-type pat_record() :: {record, loc(), RecordName::atom(),
                       [{record_field, loc(), FieldName::atom(), pat()}]}.
-type pat_record_fld_idx() ::  {record_index, loc(), RecordName::atom(), FieldName::atom()}.
-type pat_tuple() :: {tuple, loc(), [pat()]}.
-type pat_wildcard() :: {wildcard, loc()}.
-type pat_var() :: {var, loc(), local_ref_bind()}.

-type pat() :: atomic_lit() | pat_bitstring() | pat_compound() | pat_nil() | pat_cons() | pat_map()
    | pat_op() | pat_record_fld_idx() | pat_record() | pat_tuple()
    | pat_wildcard() | pat_var().

% 8.4  Expressions

-type exp_bitstring_compr() :: {bc, loc(), exp(), [qualifier()]}.
-type gen_bitstring_constr(T, U) :: {bin, loc(), [gen_bitstring_elem(T, U)]}.
-type gen_bitstring_elem(T, U) :: {bin_element,
                                   loc(),
                                   Value::T,
                                   Size::(U | default),
                                   bitstring_tyspec_list() | default}.
-type exp_bitstring_constr() :: gen_bitstring_constr(exp(), exp()).
-type exp_bitstring_elem() :: gen_bitstring_elem(exp(), exp()).
-type exp_block() :: {block, loc(), exps()}.
-type exp_case() :: {'case', loc(), exp(), [case_clause()]}.
-type exp_catch() :: {'catch', loc(), exp()}.
-type gen_cons(T) :: {cons, loc(), Head::T, Tail::T}.
-type exp_cons() :: gen_cons(exp()).
-type exp_fun_ref() :: {fun_ref, loc(), global_ref()}.
-type rec_fun_name() :: no_name | local_bind().
-type exp_fun() :: {'fun', loc(), Name::rec_fun_name(), [fun_clause()]}.
-type gen_funcall(T) :: {call, loc(), Fun::T, Args::[T]}
                      | {call_remote, loc(), Mod::T, Fun::T, Args::[T]}.
-type exp_funcall() :: gen_funcall(exp()).
-type exp_if() :: {'if', loc(), [if_clause()]}.
-type exp_list_compr() :: {lc, loc(), exp(), [qualifier()]}.
-type gen_map_create() :: {map_create, loc(), [map_assoc()]}.
-type exp_map_create() :: gen_map_create().
-type gen_map_update(T) :: {map_update, loc(), T, [map_assoc()]}.
-type exp_map_update() :: gen_map_update(exp()).
-type gen_nil() ::  {nil, loc()}.
-type exp_nil() :: gen_nil().
-type gen_binop(T) :: {op, loc(), Op::binop(), T, T}.
-type exp_binop() :: gen_binop(exp()).
-type gen_unop(T) :: {op, loc(), Op::unop(), T}.
-type exp_unop() :: gen_unop(exp()).
-type exp_recv() :: {'receive', loc(), [case_clause()]}.
-type exp_recv_after() :: {receive_after, loc(), [case_clause()], exp(), [exp()]}.
-type gen_record_create(T) :: {record_create, loc(), Name::atom(),
                               [{record_field, loc(), Field::atom(), T}]}.
-type exp_record_create() :: gen_record_create(exp()).
-type gen_record_access(T) :: {record_field, loc(), T, Name::atom(), Field::atom()}.
-type exp_record_access() :: gen_record_access(exp()).
-type gen_record_index() :: {record_index, loc(), Name::atom(), Field::atom()}.
-type exp_record_index() :: gen_record_index().
-type exp_record_update() ::  {record_update, loc(), exp(), Name::atom(),
                               [{record_field, loc(), Field::atom(), exp()}]}.
-type gen_tuple(T) ::  {tuple, loc(), [T]}.
-type exp_tuple() ::  gen_tuple(exp()).
-type exp_try() :: {'try', loc(), exps(), Cases::[case_clause()], Catches::[catch_clause()],
                    After::exps()}.
-type gen_var() :: {var, loc(), any_ref()}.
-type exp_var() :: gen_var().

% There is no match expression, because match expressions are represented as case expressions.
-type exp() :: atomic_lit() | exp_bitstring_compr() | exp_bitstring_constr() | exp_block()
    | exp_case() | exp_catch() | exp_cons() | exp_fun_ref() | exp_fun() | exp_funcall()
    | exp_if() | exp_list_compr() | exp_map_create() | exp_map_update()
    | exp_nil() | exp_binop() | exp_unop() | exp_recv() | exp_recv_after() | exp_record_create()
    | exp_record_access() | exp_record_index() | exp_record_update() | exp_tuple() | exp_try()
    | exp_var().

-type exps() :: [exp()].

-type qual_gen() ::  {generate, loc(), pat(), exp()}.
-type qual_bitstring_gen() ::  {b_generate, loc(), pat(), exp()}.
-type qualifier() :: exp() | qual_gen() | qual_bitstring_gen().

-type bitstring_tyspec() :: atom() | {atom(), Value::integer()}.
-type bitstring_tyspec_list() :: [bitstring_tyspec()].

-type map_assoc_opt() :: {map_field_assoc, loc(), exp(), exp()}.
-type map_assoc_req() :: {map_field_exact, loc(), exp(), exp()}.
-type map_assoc() :: map_assoc_opt() | map_assoc_req().

-type binop() :: atom().
-type unop() :: atom().

% 8.5  Clauses
-type catch_clause() :: {catch_clause, loc(), ExcType::exc_type_pat(), Pat::pat(),
                         Stack::stacktrace_pat(),
                         Guards::[guard()], Body::exps()}.
-type exc_type_pat() :: pat_wildcard() | pat_var() | rep_atom().
-type stacktrace_pat() :: pat_wildcard() | pat_var().

-type case_clause() :: {case_clause, loc(), Pat::pat(),   Guards::[guard()], Body::exps()}.
-type fun_clause()  :: {fun_clause, loc(), Pats::[pat()], Guards::[guard()], Body::exps()}.
-type if_clause()   :: {if_clause, loc(), Guards::[guard()], Body::exps()}.

% 8.6  Guards

% Guard sequence, AST type [guard()]
% A guard sequence is a sequence of guards, separated by semicolon. The guard sequence is true if
% at least one of the guards is true. (The remaining guards, if any, are not evaluated.)
%
% Guard, AST type guard()
% A guard is a sequence of guard tests, separated by comma (,). The guard is true if all
% guard tests evaluate to true.

-type guard() :: [guard_test()]. % list not empty
-type guard_test_bitstring_constr() :: gen_bitstring_constr(guard_test(), guard_test()).
-type guard_test_cons() :: gen_cons(guard_test()).
-type guard_test_funcall() :: gen_funcall(guard_test()).
-type guard_test_map_create() ::  gen_map_create().
-type guard_test_map_update() :: gen_map_update(guard_test()).
-type guard_test_nil() :: gen_nil().
-type guard_test_binop() :: gen_binop(guard_test()).
-type guard_test_unop() :: gen_unop(guard_test()).
-type guard_test_record_create() :: gen_record_create(guard_test()).
-type guard_test_record_access() :: gen_record_access(guard_test()).
-type guard_test_record_index() :: gen_record_index().
-type guard_test_tuple() :: gen_tuple(guard_test()).
-type guard_test_var() :: gen_var().

-type guard_test() :: atomic_lit() | guard_test_bitstring_constr() | guard_test_cons()
    | guard_test_funcall() | guard_test_map_create() | guard_test_map_update() | guard_test_nil()
    | guard_test_binop() | guard_test_unop() | guard_test_record_create()
    | guard_test_record_access() | guard_test_record_index() | guard_test_tuple()
    | guard_test_var().

% 8.7  Types
-type ty_singleton() :: {singleton, atom() | integer() | char()}.
-type ty_bitstring() :: {binary, integer(), integer()}.

-type ty_empty_list() :: {empty_list}.
-type ty_list() :: {list, ty()}.
-type ty_nonempty_list() :: {nonempty_list, ty()}.
-type ty_improper_list() :: {improper_list, ty(), ty()}.
-type ty_nonempty_improper_list() :: {nonempty_improper_list, ty(), ty()}.
-type ty_some_list() :: ty_empty_list() | ty_list() | ty_nonempty_list() | ty_improper_list()
                      | ty_nonempty_improper_list().

-type ty_simple_fun() :: {fun_simple}. % fun(): we just know it's a function
-type ty_any_arg_fun() :: {fun_any_arg, ty()}. % fun((...) -> T): we know the return type
-type ty_full_fun() :: {fun_full, [ty()], ty()}. % we know param and return types
-type ty_fun() :: ty_simple_fun() | ty_any_arg_fun() | ty_full_fun().

%% left    :: * -- X
%% right   :: X -- *
-type ty_integer_range() :: {range, integer() | '*', integer() | '*'}.
-type ty_map_any() :: {map_any}.
-type ty_map() :: {map, [ty_map_assoc()]}.
-type ty_map_assoc_opt() :: {map_field_assoc, ty(), ty()}.
-type ty_map_assoc_req() :: {map_field_exact, ty(), ty()}.
-type ty_map_assoc() :: ty_map_assoc_opt() | ty_map_assoc_req().

% Predefined types, including any() and none(). It's guaranteed that the predefined type
% is valid. Predefined types do not include tuples and lists, these types have their
% own representation.
-type predef_name() :: any | none | pid | port | reference | float | integer | atom.
-type ty_predef() :: {predef, predef_name()}.

-spec is_predef_name(atom()) -> boolean().
is_predef_name(N) ->
    case N of
        any -> true;
        none -> true;
        pid -> true;
        port -> true;
        reference -> true;
        float -> true;
        integer -> true;
        atom -> true;
        _ -> false
    end.

% Predefined type aliases. They can be expanded away, but the expansion may contain other
% predefined type aliases (see iolist for example).
-type predef_alias_name() ::
        term | binary | nonempty_binary | bitstring | nonempty_bitstring
      | boolean | byte | char | nil | number
      | list | nonempty_list | maybe_improper_list | nonempty_improper_list
      | nonempty_maybe_improper_list
      | string | nonempty_string | iodata | iolist
      | map | function | module | mfa | arity | identifier | node
      | timeout | no_return | non_neg_integer | pos_integer | neg_integer.
-type ty_predef_alias() :: {predef_alias, predef_alias_name()}.

-spec is_predef_alias_name(atom()) -> boolean().
is_predef_alias_name(N) ->
    case N of
        term -> true;
        binary -> true;
        nonempty_binary -> true;
        bitstring -> true;
        nonempty_bitstring -> true;
        boolean -> true;
        byte -> true;
        char -> true;
        nil -> true;
        number -> true;
        list -> true;
        nonempty_list -> true;
        maybe_improper_list -> true;
        nonempty_improper_list -> true;
        nonempty_maybe_improper_list -> true;
        string -> true;
        nonempty_string -> true;
        iodata -> true;
        iolist -> true;
        map -> true;
        function -> true;
        module -> true;
        mfa -> true;
        arity -> true;
        identifier -> true;
        node -> true;
        timeout -> true;
        no_return -> true;
        non_neg_integer -> true;
        pos_integer -> true;
        neg_integer -> true;
        _ -> false
    end.

-type ty_record() :: {record, atom(), [ty_field()]}.
-type ty_field() :: {atom(), ty()}.

% A reference to a user defined type. At point of construction, it's still unclear
% whether the usage is valid, so we include the location for better error reporting
% later on.
-type ty_named() :: {named, loc(), Name::global_ref(), Args::[ty()]}.

-type ty_tuple_any() :: {tuple_any}.
-type ty_tuple() :: {tuple, [ty()]}.

-type ty_var() :: {var, ty_varname()}.
-type ty_union() :: {union, [ty()]}.
-type ty_intersection() :: {intersection, [ty()]}.
-type ty_negation() :: {negation, ty()}.

-type ty() :: ty_singleton() | ty_bitstring() | ty_some_list()
    | ty_fun() | ty_integer_range() | ty_map_any() | ty_map() | ty_predef() | ty_predef_alias()
    | ty_record() | ty_named() | ty_tuple_any() | ty_tuple() | ty_var()
    | ty_union() | ty_intersection() | ty_negation().

-type ty_constraint() :: {subty_constraint, loc(), ty_varname(), ty()}.
-type bounded_tyvar() :: {ty_varname(), ty()}.
-type ty_scheme() :: {ty_scheme, [bounded_tyvar()], ty()}.


% smart constructors for intersection, union and negation
-spec mk_intersection([ast:ty()]) -> ast:ty().
mk_intersection(Tys) ->
    HasEmpty =
        lists:any(
            fun(T) ->
                case T of
                    {predef, none} -> true;
                    {negation, {predef, any}} -> true;
                    _ -> false
                end
            end,
            Tys),
    case HasEmpty of
        true -> {predef, none};
        _ ->
            Filtered =
                lists:filter(
                    fun(T) ->
                        case T of
                            {predef, any} -> false;
                            {negation, {predef, none}} -> false;
                            _ -> true
                        end
                    end,
                    Tys),
            case Filtered of
                [] -> {predef, any};
                [T] -> T;
                _ -> {intersection, Filtered}
            end
    end.


-spec mk_union([ast:ty()]) -> ast:ty().
mk_union(Tys) ->
    HasAny =
        lists:any(
            fun(T) ->
                case T of
                    {predef, any} -> true;
                    {negation, {predef, none}} -> true;
                    _ -> false
                end
            end,
            Tys),
    case HasAny of
        true -> {predef, any};
        _ ->
            Filtered =
                lists:filter(
                    fun(T) ->
                        case T of
                            {predef, none} -> false;
                            [] -> error(todo);
                            _ -> true
                        end
                    end,
                    Tys),
            case Filtered of
                [] -> {predef, none};
                [T] -> T;
                _ -> {union, Filtered}
            end
    end.

-spec mk_negation(ast:ty()) -> ast:ty().
mk_negation({predef, any}) -> {predef, none};
mk_negation({predef, none}) -> {predef, any};
mk_negation(T) -> {negation, T}.

erlang_ty_to_ast(X) ->
    ty_rec:transform(
        X,
        #{
            to_fun => fun(S, T) -> stdtypes:tfun_full(lists:map(fun(F) -> erlang_ty_to_ast(F) end,S), erlang_ty_to_ast(T)) end,
            to_tuple => fun(Ts) -> stdtypes:ttuple(lists:map(fun(T) -> erlang_ty_to_ast(T) end,Ts)) end,
            to_atom => fun(A) -> stdtypes:tatom(A) end,
            to_int => fun(X, Y) -> stdtypes:trange(X, Y) end,
            to_predef => fun('[]') -> stdtypes:tempty_list(); (Predef) -> {predef, Predef} end,
            any_tuple => fun stdtypes:ttuple_any/0,
            any_fun => fun stdtypes:tfun_any/0,
            any_int => fun stdtypes:tint/0,
            any_atom => fun stdtypes:tatom/0,
            any_predef => fun stdtypes:tspecial_any/0,
            empty => fun stdtypes:tnone/0,
            any => fun stdtypes:tany/0,
            var => fun({var, Id, Name}) ->
                Object = ets:lookup(?VAR_ETS, Name),
                case Object of
                    % new variable not seen before!
                    [] -> {var, list_to_atom("mu" ++ integer_to_list(Id))};
                    [{_, _}] -> {var, Name}
                end
                   end,
            union => fun ast:mk_union/1,
            intersect => fun ast:mk_intersection/1,
            negate => fun ast:mk_negation/1
        }).

ast_to_erlang_ty({singleton, Atom}) when is_atom(Atom) ->
    TyAtom = ty_atom:finite([Atom]),
    TAtom = dnf_var_ty_atom:ty_atom(TyAtom),
    ty_rec:atom(TAtom);
ast_to_erlang_ty({singleton, IntOrChar}) ->
    Int = dnf_var_int:int(ty_interval:interval(IntOrChar, IntOrChar)),
    ty_rec:interval(Int);
% TODO
ast_to_erlang_ty({binary, _, _}) ->
    erlang:error("Bitstrings not implemented yet");

ast_to_erlang_ty({tuple_any}) ->
    ty_rec:tuple();
ast_to_erlang_ty({tuple, Comps}) ->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T) end, Comps),

    T = dnf_var_ty_tuple:tuple(dnf_ty_tuple:tuple(ty_tuple:tuple(ETy))),
    ty_rec:tuple(length(Comps), T);

% funs
ast_to_erlang_ty({fun_simple}) ->
    ty_rec:function();
ast_to_erlang_ty({fun_full, Comps, Result}) ->
    ETy = lists:map(fun(T) -> ast_to_erlang_ty(T) end, Comps),
    TyB = ast_to_erlang_ty(Result),

    T = dnf_var_ty_function:function(dnf_ty_function:function(ty_function:function(ETy, TyB))),
    ty_rec:function(length(Comps), T);

% var
ast_to_erlang_ty({var, A}) ->
    ty_rec:variable(maybe_new_variable(A));

% ty_some_list
ast_to_erlang_ty({list, Ty}) -> ty_rec:union( ast_to_erlang_ty({improper_list, Ty, {empty_list}}), ast_to_erlang_ty({empty_list}) );
ast_to_erlang_ty({nonempty_list, Ty}) -> ast_to_erlang_ty({nonempty_improper_list, Ty, {empty_list}});
ast_to_erlang_ty({nonempty_improper_list, Ty, Term}) -> ty_rec:diff(ast_to_erlang_ty({list, Ty}), ast_to_erlang_ty(Term));
ast_to_erlang_ty({improper_list, _Ty, _Term}) ->
    erlang:error("Lists not implemented yet");
ast_to_erlang_ty({empty_list}) ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef('[]')));
ast_to_erlang_ty({predef, T}) when T == pid; T == port; T == reference; T == float ->
    ty_rec:predef(dnf_var_predef:predef(ty_predef:predef(T)));

% named
ast_to_erlang_ty({named, _, _Ref, _Args}) ->
    erlang:error("named references not implemented yet");

% ty_predef_alias
ast_to_erlang_ty({predef_alias, Alias}) ->
    ast_to_erlang_ty(stdtypes:expand_predef_alias(Alias));

% ty_predef
ast_to_erlang_ty({predef, atom}) ->
    Atom = dnf_var_ty_atom:any(),
    ty_rec:atom(Atom);

ast_to_erlang_ty({predef, any}) -> ty_rec:any();
ast_to_erlang_ty({predef, none}) -> ty_rec:empty();
ast_to_erlang_ty({predef, integer}) ->
    ty_rec:interval();

% ints
ast_to_erlang_ty({range, From, To}) ->
    Int = dnf_var_int:int(ty_interval:interval(From, To)),
    ty_rec:interval(Int);

ast_to_erlang_ty({union, []}) -> ty_rec:empty();
ast_to_erlang_ty({union, [A]}) -> ast_to_erlang_ty(A);
ast_to_erlang_ty({union, [A|T]}) -> ty_rec:union(ast_to_erlang_ty(A), ast_to_erlang_ty({union, T}));

ast_to_erlang_ty({intersection, []}) -> ty_rec:any();
ast_to_erlang_ty({intersection, [A]}) -> ast_to_erlang_ty(A);
ast_to_erlang_ty({intersection, [A|T]}) -> ty_rec:intersect(ast_to_erlang_ty(A), ast_to_erlang_ty({intersection, T}));

ast_to_erlang_ty({negation, Ty}) -> ty_rec:negate(ast_to_erlang_ty(Ty));

ast_to_erlang_ty(T) ->
    logger:error("Norm not implemented for~n~p", [T]),
    erlang:error("Norm not implemented, see error log").

ast_to_erlang_ty_var({var, Name}) when is_atom(Name) ->
    maybe_new_variable(Name).

maybe_new_variable(Name) ->
    Object = ets:lookup(?VAR_ETS, Name),
    case Object of
        [] ->
            Var = ty_variable:new(Name),
            ets:insert(?VAR_ETS, {Name, Var}),
            Var;
        [{_, Variable}] -> Variable
    end.
