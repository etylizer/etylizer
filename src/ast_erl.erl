-module(ast_erl).
% This header file defines type specifications for erlang parse trees.
% Description of parse tree: http://erlang.org/doc/apps/erts/absform.html

% generated via
% grep -o '^-type [a-zA-Z_0-9]*' src/ast_erl.erl | sed 's/-type //g' | grep -v '^gen_' | grep -v '^list[0-9]' | sed 's/^/    /g; s|$|/0,|g'
-export_type([
    anno/0,
    fun_with_arity/0,
    export_form/0,
    export_type_form/0,
    import_form/0,
    file_form/0,
    mod_form/0,
    fun_decl/0,
    fun_spec_q/0,
    fun_spec_unq/0,
    fun_spec/0,
    record_decl/0,
    type_decl/0,
    wild_attr/0,
    eof/0,
    warnings_errors/0,
    form/0,
    forms/0,
    untyped_record_field/0,
    record_field/0,
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
    pat_binop/0,
    pat_unop/0,
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
    exp_fun_qref/0,
    exp_fun/0,
    exp_named_fun/0,
    exp_funcall/0,
    exp_funcall_q/0,
    exp_if/0,
    exp_list_compr/0,
    exp_map_create/0,
    exp_map_update/0,
    exp_map_compr/0,
    exp_match/0,
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
    qual_list_gen/0,
    qual_map_gen/0,
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
    exc_type_pat/0,
    catch_clause_header/0,
    catch_clause/0,
    fun_clause/0,
    if_clause/0,
    guard/0,
    guard_test_bitstring_constr/0,
    guard_test_cons/0,
    guard_test_funcall/0,
    guard_test_funcall_q/0,
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
    ty_ann/0,
    ty_lit/0,
    ty_bitstring/0,
    ty_empty_list/0,
    ty_list/0,
    ty_fun_unconstrained_ty/0,
    ty_fun_constrained_ty/0,
    ty_fun_constraint/0,
    ty_constraint/0,
    ty_simple_fun/0,
    ty_any_arg_fun/0,
    ty_fun/0,
    ty_integer_range/0,
    ty_map_any/0,
    ty_map/0,
    ty_map_assoc_opt/0,
    ty_map_assoc_req/0,
    ty_map_assoc/0,
    ty_binop/0,
    ty_unop/0,
    ty_predef/0,
    ty_record/0,
    ty_field/0,
    ty_remote/0,
    ty_tuple_any/0,
    ty_tuple/0,
    ty_union/0,
    ty_var/0,
    ty_user/0,
    ty_full_fun/0,
    ty/0,
    tydef/0
]).

-export([ty_varname/1, user_tyname/1]).

% At several places, the AST contains lists with a fixed number of elements in a fixed order.
% Such types are not expressible in erlang's type syntax. So we introduce various type synonyms
% to clarify the intention.

% Lists with exactly three elements.
-type list3(T, U, V) :: [T | U | V].

% Lists with exactly two elements.
-type list2(T, U) :: [T | U].
-type list2(T) :: [T].

% A list containing exactly one element of type T
-type list1(T) :: [T].

% A list with first element of type T and then arbitrary manu Us.
-type list1star(T, U) :: [T | U].


% 8.1  Module Declarations and Forms
-type anno() :: any(). % Should be erl_anno:anno() but ast_check.erl cannot handle this.
-type fun_with_arity() :: {atom(), integer()}.
-type ty_with_arity() :: {atom(), integer()}.
-type export_form() :: {attribute, anno(), export, [fun_with_arity()]}.
-type export_type_form() :: {attribute, anno(), export_type, [ty_with_arity()]}.
-type import_form() :: {attribute, anno(), import, {Mod::atom(),[fun_with_arity()]}}.
-type file_form() :: {attribute, anno(), file, {File::string(), Line::integer()}}.
-type mod_form() :: {attribute, anno(), module, Mod::atom()}.
-type behavior_form() :: {attribute, anno(), behavior | behaviour, Mod::atom()}.
-type other_attr_form() :: {attribute, anno(), atom(), term()}.
-type fun_decl() :: {function, anno(), Name::atom(), Arity::integer(), [fun_clause()]}.
-type fun_spec_q() :: {attribute, anno(), spec, {{Mod::atom(), Name::atom(), Arity::integer()},
                                                 [ty_full_fun()]}}.
-type fun_spec_unq() :: {attribute, anno(), spec | callback, {{Name::atom(), Arity::integer()},
                                                              [ty_full_fun()]}}.
-type fun_spec() :: fun_spec_q() | fun_spec_unq().
-type record_decl() :: {attribute, anno(), record, {Name::atom(),[record_field()]}}.
-type type_decl() :: {attribute, anno(), type|opaque, tydef()}.
-type tydef() :: {Name::atom(), Rhs::ty(), [ty_var()]}.
-type wild_attr() :: {attribute, anno(), atom(), term()}.
-type eof() :: {eof, anno()}.
-type warnings_errors() :: {error, any()} | {warning, any()}.

-type form() :: export_form() | export_type_form() | behavior_form()
    | import_form() | file_form() | mod_form() | fun_decl()
    | fun_spec() | record_decl() | type_decl() | wild_attr() | other_attr_form()
    | eof() | warnings_errors().
-type forms() :: [form()].

-type untyped_record_field() :: {record_field, anno(), rep_atom()}
    | {record_field, anno(), rep_atom(), exp()}.

-type record_field() :: untyped_record_field()
    | {typed_record_field, untyped_record_field(), ty()}.

% 8.2  Atomic Literals
-type rep_atom() :: {'atom', anno(), atom()}.
-type rep_char() :: {'char', anno(), char()}.
-type rep_float() :: {'float', anno(), float()}.
-type rep_integer() :: {'integer', anno(), integer()}.
-type rep_string() :: {'string', anno(), [char()]}.

-type atomic_lit() :: rep_atom() | rep_char() | rep_float() | rep_integer() | rep_string().

% 8.3  Patterns

-type pat_bitstring() :: {bin, anno(), [pat_bitstring_elem()]}.
-type pat_bitstring_elem() :: gen_bitstring_elem(pat(), exp()).
-type pat_compound() :: {match, anno(), pat(), pat()}. %  P_1 = P_2
-type pat_nil() :: {nil, anno()}.
-type pat_cons() :: {cons, anno(), pat(), pat()}.
-type pat_map() :: {map, anno(), [pat_map_assoc()]}. %  #{A_1, ..., A_k} with Ai: P_i_1 := P_i_2
-type pat_map_assoc() :: {map_field_exact, anno(), pat(), pat()}.
-type pat_binop() :: {op, anno(), atom(), pat(), pat()}.
-type pat_unop() :: {op, anno(), atom(), pat()}.
-type pat_record() :: {record, anno(), Name::atom(),
                       [{record_field, anno(), Field::rep_atom(), pat()}]}.
-type pat_record_fld_idx() ::  {record_index, anno(), Name::atom(), rep_atom()}.
-type pat_tuple() :: {tuple, anno(), [pat()]}.
-type pat_wildcard() :: {var, anno(), '_'}.
-type pat_var() :: {var, anno(), Var::atom()}.

-type pat() :: atomic_lit() | pat_bitstring() | pat_compound() | pat_cons() | pat_map()
    | pat_nil() | pat_binop() | pat_unop() | pat_record_fld_idx() | pat_record() | pat_tuple()
    | pat_wildcard() | pat_var().

% 8.4  Expressions

-type exp_bitstring_compr() :: {bc, anno(), exp(), [qualifier()]}.
-type gen_bitstring_constr(T, U) :: {bin, anno(), [gen_bitstring_elem(T, U)]}.
-type gen_bitstring_elem(T, U) :: {bin_element,
                                   anno(),
                                   Value::T,
                                   Size::(U | default),
                                   bitstring_tyspec_list() | default}.
-type exp_bitstring_constr() :: gen_bitstring_constr(exp(), exp()).
-type exp_bitstring_elem() :: gen_bitstring_elem(exp(), exp()).
-type exp_block() :: {block, anno(), exps()}.
-type exp_case() :: {'case', anno(), exp(), [case_clause()]}.
-type exp_catch() :: {'catch', anno(), exp()}.
-type gen_cons(T) :: {cons, anno(), Head::T, Tail::T}.
-type exp_cons() :: gen_cons(exp()).

% fun Name/Arity or fun Mod:Name/Arity
-type exp_fun_ref() :: {'fun', anno(), {function, Name::atom(), Arity::integer()}}.
-type exp_fun_qref() :: {'fun', anno(), {function, Mod::rep_atom(), Name::rep_atom(),
                                         Arity::rep_integer()}}.
-type exp_fun() :: {'fun', anno(), {clauses, [fun_clause()]}}.
-type exp_named_fun() :: {named_fun, anno(), Name::atom(), [fun_clause()]}.
-type gen_funcall(T) :: {call, anno(), Fun::T, Args::[T]}.
-type exp_funcall() :: gen_funcall(exp()).
-type gen_funcall_q(T) :: {call, anno(), {remote, anno(), Mod::T, Fun::T}, Args::[T]}.
-type exp_funcall_q() :: gen_funcall_q(exp()).
-type exp_if() :: {'if', anno(), [if_clause()]}.
-type exp_list_compr() :: {lc, anno(), exp(), [qualifier()]}.
-type gen_map_create() :: {map, anno(), [map_assoc()]}.
-type exp_map_create() :: gen_map_create().
-type gen_map_update(T) :: {map, anno(), T, [map_assoc()]}.
-type exp_map_update() :: gen_map_update(exp()).
-type exp_map_compr() :: {mc, anno(), map_assoc_opt(), [qualifier()]}.
-type exp_match() :: {match, anno(), pat(), exp()}.
-type gen_nil() ::  {nil, anno()}.
-type exp_nil() :: gen_nil().
-type gen_binop(T) :: {op, anno(), Op::binop(), T, T}.
-type exp_binop() :: gen_binop(exp()).
-type gen_unop(T) :: {op, anno(), Op::unop(), T}.
-type exp_unop() :: gen_unop(exp()).
-type exp_recv() :: {'receive', anno(), [case_clause()]}.
-type exp_recv_after() :: {'receive', anno(), [case_clause()], exp(), [exp()]}.
-type gen_record_create(T) :: {record, anno(), Name::atom(),
                               [{record_field, anno(), Field::rep_atom(), T}]}.
-type exp_record_create() :: gen_record_create(exp()).
-type gen_record_access(T) :: {record_field, anno(), T, Name::atom(), Field::rep_atom()}.
-type exp_record_access() :: gen_record_access(exp()).
-type gen_record_index() :: {record_index, anno(), Name::atom(), Field::rep_atom()}.
-type exp_record_index() :: gen_record_index().
-type exp_record_update() ::  {record, anno(), exp(), Name::atom(),
                               [{record_field, anno(), Field::rep_atom(), exp()}]}.
-type gen_tuple(T) ::  {tuple, anno(), [T]}.
-type exp_tuple() ::  gen_tuple(exp()).
-type exp_try() :: {'try', anno(), exps(), Cases::[case_clause()], Catches::[catch_clause()],
                    After::exps()}.
-type gen_var() :: {var, anno(), Var::atom()}.
-type exp_var() :: gen_var().

-type exp() :: atomic_lit() | exp_bitstring_compr() | exp_bitstring_constr() | exp_block()
    | exp_case() | exp_catch() | exp_cons() | exp_fun_ref() | exp_fun_qref() | exp_fun()
    | exp_named_fun() | exp_funcall() | exp_funcall_q() | exp_if() | exp_list_compr()
    | exp_map_create() | exp_map_update() | exp_map_compr()
    | exp_match() | exp_nil() | exp_binop() | exp_unop()
    | exp_recv() | exp_recv_after() | exp_record_create() | exp_record_access()
    | exp_record_index() | exp_record_update() | exp_tuple() | exp_try() | exp_var().

-type exps() :: [exp()].

-type qual_list_gen() ::  {generate, anno(), pat(), exp()}.
-type qual_bitstring_gen() ::  {b_generate, anno(), pat(), exp()}.
-type qual_map_gen() ::  {m_generate, anno(), {map_field_exact, anno(), pat(), pat()}, exp()}.
-type qualifier() :: exp() | qual_list_gen() | qual_bitstring_gen() | qual_map_gen().

-type bitstring_tyspec() :: atom() | {atom(), Value::integer()}.
-type bitstring_tyspec_list() :: [bitstring_tyspec()].

-type map_assoc_opt() :: {map_field_assoc, anno(), exp(), exp()}.
-type map_assoc_req() :: {map_field_exact, anno(), exp(), exp()}.
-type map_assoc() :: map_assoc_opt() | map_assoc_req().

-type binop() :: atom().
-type unop() :: atom().

% 8.5  Clauses
-type catch_clause() :: {clause, anno(), Header::list1(catch_clause_header()), Guards::[guard()],
                         Body::exps()}.
-type exc_type_pat() :: rep_atom() | pat_var().
-type catch_clause_header() :: {tuple, anno(),
                                [X::exc_type_pat() | P::pat() | S::pat_var()]}.
                                 % The order is always X, P, S.
                                 % - X is the exception type (a variable or one of the atoms
                                 %   'throw', 'exit' or 'error'.
                                 % - P is a pattern
                                 % - S is a wildcard or variable for the stacktrace.

-type case_clause()  :: {clause, anno(), Pats::list1(pat()), Guards::[guard()], Body::exps()}.
-type fun_clause()   :: {clause, anno(), Pats::[pat()],      Guards::[guard()], Body::exps()}.
-type if_clause()    :: {clause, anno(), Pats::[],           Guards::[guard()], Body::exps()}.

% 8.6  Guards
-type guard() :: list1(guard_test()).
-type guard_test_bitstring_constr() :: gen_bitstring_constr(guard_test(), guard_test()).
-type guard_test_cons() :: gen_cons(guard_test()).
-type guard_test_funcall() :: gen_funcall(guard_test()).
-type guard_test_funcall_q() :: gen_funcall_q(guard_test()).
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
    | guard_test_funcall() | guard_test_funcall_q() | guard_test_map_create()
    | guard_test_map_update() | guard_test_nil()
    | guard_test_binop() | guard_test_unop() | guard_test_record_create()
    | guard_test_record_access() | guard_test_record_index() | guard_test_tuple()
    | guard_test_var().

% 8.7  Types

-type ty_ann() :: {ann_type, anno(), list2(Var::exp_var(), Ty::ty())}. % annotation A::T in type specs
-type ty_lit() :: rep_atom() | rep_integer() | rep_char().
-type ty_bitstring() :: {type, anno(), binary, list2(rep_integer())}.
-type ty_empty_list() :: {type, anno(), nil, []}.
-type ty_list() :: {type, anno(), list, list1(ty())}.

-type ty_full_fun() :: ty_fun_unconstrained_ty() | ty_fun_constrained_ty().
-type ty_fun_unconstrained_ty() :: % fun((T1...Tn) -> T)
    {type, anno(), 'fun', list2({type, anno(), product, [ty()]}, ty())}.
-type ty_fun_constrained_ty() ::   % fun((T1...Tn) -> T) when Fc
    {type, anno(), bounded_fun, list2(ty_fun_unconstrained_ty(), ty_fun_constraint())}.
-type ty_fun_constraint() :: [ty_constraint()].
-type ty_constraint() :: {type, anno(), constraint, list2({atom,anno(),is_subtype}, list2(ty_var(), ty()))}.

-type ty_simple_fun() :: {type, anno(), 'fun', []}. % fun()
-type ty_any_arg_fun() :: {type, anno(),'fun', list2({type, anno(), any}, ty())}. % fun(...) -> T
-type ty_fun() :: ty_simple_fun() | ty_any_arg_fun() | ty_full_fun().

-type ty_integer_range() :: {type, anno(), range, list2(rep_integer())}.
-type ty_map_any() :: {type, anno(), map, any}.
-type ty_map() :: {type, anno(), map, [ty_map_assoc()]}.
-type ty_map_assoc_opt() :: {type, anno(), map_field_assoc, list2(ty())}.
-type ty_map_assoc_req() :: {type, anno(), map_field_exact, list2(ty())}.
-type ty_map_assoc() :: ty_map_assoc_opt() | ty_map_assoc_req().
% The types ty_binop and ty_unop denote expressions that can be evaluated to an integer
% at compile time.
-type ty_binop() :: {op, anno(), binop(), ty(), ty()}.
-type ty_unop() :: {op, anno(), unop(), ty()}.
-type ty_predef() :: {type, anno(), atom(), [ty()]}.
-type ty_record() :: {type, anno(), record, list1star(Name::rep_atom(), ty_field())}.
-type ty_field() :: {type, anno(), field_type, list2(Name::rep_atom(), ty())}.
-type ty_remote() :: {remote_type, anno(), list3(Module::rep_atom(), Name::rep_atom(), Args::[ty()])}.
-type ty_tuple_any() :: {type, anno(), tuple, any}.
-type ty_tuple() :: {type, anno(), tuple, [ty()]}.
-type ty_union() :: {type, anno(), union, [ty()]}.
-type ty_var() :: {var, anno(), Name::atom()}.
-type ty_user() :: {user_type, anno(), Name::atom(), Args::[ty()]}.

-type ty() :: ty_ann() | ty_lit() | ty_bitstring() | ty_empty_list() | ty_list()
    | ty_fun() | ty_integer_range() | ty_map_any() | ty_map() | ty_binop() | ty_unop() | ty_predef()
    | ty_record() | ty_remote() | ty_tuple_any() | ty_tuple() | ty_union() | ty_var() | ty_user().

-spec ty_varname(ty_var()) -> atom().
ty_varname({var, _, Name}) -> Name.

-spec user_tyname(ty_user()) -> atom().
user_tyname({user_type, _, Name, _}) -> Name.
