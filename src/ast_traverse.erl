-module(ast_traverse).

% @doc Typed traversals of the internal AST (see ast.erl).
%
% utils:everything/2 and utils:everywhere/2 traverse arbitrary terms, so their callbacks
% only ever see term() and their results cannot be typed without rank-2 polymorphism.
% This module provides typed replacements for the AST:
%
% - everything/2 is a generic query, just like utils:everything/2. It does not know the
%   structure of the AST; that is described by the type external_types:subterm() alone.
%   The callback receives such a subterm and can match on it precisely.
% - map_locs_forms/2 and friends rebuild the AST. Rebuilding has to preserve the sort of
%   every node (a pattern must stay a pattern), so these functions follow the structure
%   of the AST explicitly. Only locations can be changed.
% - ty_everywhere/2 replaces types inside of types.

-export([
    everything/2,
    subterms/1,
    ty_everywhere/2,
    ty_descend/2,
    map_locs_forms/2,
    map_locs_ty/2,
    map_locs_tys/2,
    map_locs_ty_scheme/2
]).

-export_type([
    loc_fun/0
]).

% Rewrites a location.
-type loc_fun() :: fun((ast:loc()) -> ast:loc()).

%% ---------------------------------------------------------------------------
%% Queries
%% ---------------------------------------------------------------------------

% Collects all results R where the given function returns {ok, R} or {rec, R} for one of
% the given terms or a subterm of them. {ok, R} collects R and does not descend into the
% term; {rec, R} collects R and descends; error just descends.
% Subterms are visited in the order in which they appear in the AST.
-spec everything(fun((external_types:subterm()) -> {ok, R} | {rec, R} | error),
                 [external_types:subterm()]) -> [R].
everything(F, Terms) ->
    utils:everything(fun subterms/1, F, Terms).

% The direct subterms of a term: the elements of a list and the components of a tuple.
% This function does not know the AST. That it type checks proves that
% external_types:subterm() is closed, so the function given to everything/2 is only ever
% applied to such a subterm.
-spec subterms(external_types:subterm()) -> [external_types:subterm()].
subterms({attribute, Loc, compile, _}) -> [attribute, Loc, compile];
subterms([H | T]) -> [H | subterms(T)];
subterms({A}) -> [A];
subterms({A, B}) -> [A, B];
subterms({A, B, C}) -> [A, B, C];
subterms({A, B, C, D}) -> [A, B, C, D];
subterms({A, B, C, D, E}) -> [A, B, C, D, E];
subterms({A, B, C, D, E, F}) -> [A, B, C, D, E, F];
subterms({A, B, C, D, E, F, G}) -> [A, B, C, D, E, F, G];
subterms(_) -> [].

%% ---------------------------------------------------------------------------
%% Transformations of types
%% ---------------------------------------------------------------------------

% Replaces types inside of a type. The function given is applied to the type and all types
% below it: {ok, T} replaces the type by T and does not descend into T; {rec, T} replaces
% the type and continues with T; error just descends.
-spec ty_everywhere(fun((ast:ty()) -> {ok, ast:ty()} | {rec, ast:ty()} | error), ast:ty()) -> ast:ty().
ty_everywhere(F, Ty) ->
    utils:everywhere(fun ty_descend/2, F, Ty).

% Applies the given function to the direct subtypes of a type.
% The variable bound by a recursive type is left alone.
-spec ty_descend(fun((ast:ty()) -> ast:ty()), ast:ty()) -> ast:ty().
ty_descend(F, {list, A}) -> {list, F(A)};
ty_descend(F, {cons, A, B}) -> {cons, F(A), F(B)};
ty_descend(F, {bitstring_cons, A, B}) -> {bitstring_cons, F(A), F(B)};
ty_descend(F, {nonempty_list, A}) -> {nonempty_list, F(A)};
ty_descend(F, {improper_list, A, B}) -> {improper_list, F(A), F(B)};
ty_descend(F, {nonempty_improper_list, A, B}) -> {nonempty_improper_list, F(A), F(B)};
ty_descend(F, {fun_any_arg, R}) -> {fun_any_arg, F(R)};
ty_descend(F, {fun_full, Args, R}) -> {fun_full, lists:map(F, Args), F(R)};
ty_descend(F, {map, Assocs}) ->
    {map, lists:map(fun({Kind, K, V}) -> {Kind, F(K), F(V)} end, Assocs)};
ty_descend(F, {named, L, Ref, Args}) -> {named, L, Ref, lists:map(F, Args)};
ty_descend(F, {tuple, Args}) -> {tuple, lists:map(F, Args)};
ty_descend(F, {union, Args}) -> {union, lists:map(F, Args)};
ty_descend(F, {intersection, Args}) -> {intersection, lists:map(F, Args)};
ty_descend(F, {negation, A}) -> {negation, F(A)};
ty_descend(F, {mu, V, A}) -> {mu, V, F(A)};
ty_descend(_, T) -> T.

% Applies the given function to every location in the given type.
-spec map_locs_ty(loc_fun(), ast:ty()) -> ast:ty().
map_locs_ty(FL, {named, L, Ref, Args}) -> {named, FL(L), Ref, map_locs_tys(FL, Args)};
map_locs_ty(FL, T) -> ty_descend(fun(U) -> map_locs_ty(FL, U) end, T).

-spec map_locs_tys(loc_fun(), [ast:ty()]) -> [ast:ty()].
map_locs_tys(FL, Tys) -> lists:map(fun(T) -> map_locs_ty(FL, T) end, Tys).

-spec map_locs_ty_scheme(loc_fun(), ast:ty_scheme()) -> ast:ty_scheme().
map_locs_ty_scheme(FL, {ty_scheme, Vars, Body}) ->
    {ty_scheme, lists:map(fun({V, Bound}) -> {V, map_locs_ty(FL, Bound)} end, Vars), map_locs_ty(FL, Body)}.

%% ---------------------------------------------------------------------------
%% Transformations of forms
%% ---------------------------------------------------------------------------

% Applies the given function to every location in the given forms.
-spec map_locs_forms(loc_fun(), ast:forms()) -> ast:forms().
map_locs_forms(FL, Forms) -> lists:map(fun(F) -> m_form(FL, F) end, Forms).

-spec m_form(loc_fun(), ast:form()) -> ast:form().
m_form(FL, {function, L, Name, Arity, Args, Body}) ->
    {function, FL(L), Name, Arity, Args, m_exps(FL, Body)};
m_form(FL, {attribute, L, Kind, Name, Arity, TyScm, Mod}) ->
    {attribute, FL(L), Kind, Name, Arity, map_locs_ty_scheme(FL, TyScm), Mod};
m_form(FL, {attribute, L, type, Vis, {Name, TyScm}}) ->
    {attribute, FL(L), type, Vis, {Name, map_locs_ty_scheme(FL, TyScm)}};
m_form(FL, {attribute, L, record, {Name, Fields}}) ->
    {attribute, FL(L), record, {Name, lists:map(fun(F) -> m_record_decl_field(FL, F) end, Fields)}};
m_form(FL, {attribute, L, export, X}) -> {attribute, FL(L), export, X};
m_form(FL, {attribute, L, export_type, X}) -> {attribute, FL(L), export_type, X};
m_form(FL, {attribute, L, import, X}) -> {attribute, FL(L), import, X};
m_form(FL, {attribute, L, module, X}) -> {attribute, FL(L), module, X};
m_form(FL, {attribute, L, compile, X}) -> {attribute, FL(L), compile, X};
m_form(FL, {attribute, L, etylizer, {msg_type, Name, Arity, Ty}}) ->
    {attribute, FL(L), etylizer, {msg_type, Name, Arity, m_msg_ty(FL, Ty)}};
m_form(FL, {attribute, L, etylizer, {msg_type, Name, Arity, Ty, noexhaustiveness}}) ->
    {attribute, FL(L), etylizer, {msg_type, Name, Arity, m_msg_ty(FL, Ty), noexhaustiveness}};
m_form(FL, {attribute, L, etylizer, X}) -> {attribute, FL(L), etylizer, X}.

-spec m_msg_ty(loc_fun(), ast:ty() | [ast:ty_full_fun()]) -> ast:ty() | [ast:ty_full_fun()].
m_msg_ty(FL, FunTys) when is_list(FunTys) ->
    lists:map(fun({fun_full, Args, Res}) -> {fun_full, map_locs_tys(FL, Args), map_locs_ty(FL, Res)} end,
              FunTys);
m_msg_ty(FL, Ty) -> map_locs_ty(FL, Ty).

-spec m_record_decl_field(loc_fun(), ast:record_field()) -> ast:record_field().
m_record_decl_field(FL, {record_field, L, Name, Ty, Default}) ->
    NewTy = case Ty of untyped -> untyped; _ -> map_locs_ty(FL, Ty) end,
    NewDefault = case Default of no_default -> no_default; _ -> m_exp(FL, Default) end,
    {record_field, FL(L), Name, NewTy, NewDefault}.

-spec m_case_clauses(loc_fun(), [ast:case_clause()]) -> [ast:case_clause()].
m_case_clauses(FL, Clauses) -> lists:map(fun(C) -> m_case_clause(FL, C) end, Clauses).

-spec m_case_clause(loc_fun(), ast:case_clause()) -> ast:case_clause().
m_case_clause(FL, {case_clause, L, Pat, Guards, Body}) ->
    {case_clause, FL(L), m_pat(FL, Pat), m_guards(FL, Guards), m_exps(FL, Body)}.

-spec m_catch_clause(loc_fun(), ast:catch_clause()) -> ast:catch_clause().
m_catch_clause(FL, {catch_clause, L, Exc, Pat, Stack, Guards, Body}) ->
    {catch_clause, FL(L), m_exc_type_pat(FL, Exc), m_pat(FL, Pat), m_stacktrace_pat(FL, Stack),
     m_guards(FL, Guards), m_exps(FL, Body)}.

-spec m_exc_type_pat(loc_fun(), ast:exc_type_pat()) -> ast:exc_type_pat().
m_exc_type_pat(FL, {wildcard, L}) -> {wildcard, FL(L)};
m_exc_type_pat(FL, {var, L, Ref}) -> {var, FL(L), Ref};
m_exc_type_pat(FL, {atom, L, A}) -> {atom, FL(L), A}.

-spec m_stacktrace_pat(loc_fun(), ast:stacktrace_pat()) -> ast:stacktrace_pat().
m_stacktrace_pat(FL, {wildcard, L}) -> {wildcard, FL(L)};
m_stacktrace_pat(FL, {var, L, Ref}) -> {var, FL(L), Ref}.

-spec m_exps(loc_fun(), [ast:exp()]) -> [ast:exp()].
m_exps(FL, Es) -> lists:map(fun(E) -> m_exp(FL, E) end, Es).

-spec m_exp(loc_fun(), ast:exp()) -> ast:exp().
m_exp(FL, {atom, L, A}) -> {atom, FL(L), A};
m_exp(FL, {char, L, C}) -> {char, FL(L), C};
m_exp(FL, {float, L, F}) -> {float, FL(L), F};
m_exp(FL, {integer, L, I}) -> {integer, FL(L), I};
m_exp(FL, {string, L, S}) -> {string, FL(L), S};
m_exp(FL, {nil, L}) -> {nil, FL(L)};
m_exp(FL, {var, L, Ref}) -> {var, FL(L), Ref};
m_exp(FL, {fun_ref, L, Ref}) -> {fun_ref, FL(L), Ref};
m_exp(FL, {bc, L, E, Qs}) -> {bc, FL(L), m_exp(FL, E), m_qualifiers(FL, Qs)};
m_exp(FL, {bin, L, Elems}) -> {bin, FL(L), lists:map(fun(El) -> m_exp_bin_elem(FL, El) end, Elems)};
m_exp(FL, {block, L, Es}) -> {block, FL(L), m_exps(FL, Es)};
m_exp(FL, {'case', L, E, Clauses}) -> {'case', FL(L), m_exp(FL, E), m_case_clauses(FL, Clauses)};
m_exp(FL, {'catch', L, E}) -> {'catch', FL(L), m_exp(FL, E)};
m_exp(FL, {cons, L, Hd, Tl}) -> {cons, FL(L), m_exp(FL, Hd), m_exp(FL, Tl)};
m_exp(FL, {fun_ref_dyn, L, {qref_dyn, M, F, A}}) ->
    {fun_ref_dyn, FL(L), {qref_dyn, m_exp(FL, M), m_exp(FL, F), m_exp(FL, A)}};
m_exp(FL, {'fun', L, Name, Args, Body}) -> {'fun', FL(L), Name, Args, m_exps(FL, Body)};
m_exp(FL, {call, L, F, Args}) -> {call, FL(L), m_exp(FL, F), m_exps(FL, Args)};
m_exp(FL, {call_remote, L, M, F, Args}) ->
    {call_remote, FL(L), m_exp(FL, M), m_exp(FL, F), m_exps(FL, Args)};
m_exp(FL, {lc, L, E, Qs}) -> {lc, FL(L), m_exp(FL, E), m_qualifiers(FL, Qs)};
m_exp(FL, {map_create, L, Assocs}) ->
    {map_create, FL(L), lists:map(fun(A) -> m_map_assoc_opt(FL, A) end, Assocs)};
m_exp(FL, {map_update, L, E, Assocs}) -> {map_update, FL(L), m_exp(FL, E), m_map_assocs(FL, Assocs)};
m_exp(FL, {mc, L, K, V, Qs}) -> {mc, FL(L), m_exp(FL, K), m_exp(FL, V), m_qualifiers(FL, Qs)};
m_exp(FL, {op, L, Op, A, B}) -> {op, FL(L), Op, m_exp(FL, A), m_exp(FL, B)};
m_exp(FL, {op, L, Op, A}) -> {op, FL(L), Op, m_exp(FL, A)};
m_exp(FL, {'receive', L, Clauses}) -> {'receive', FL(L), m_case_clauses(FL, Clauses)};
m_exp(FL, {receive_after, L, Clauses, Timeout, Body}) ->
    {receive_after, FL(L), m_case_clauses(FL, Clauses), m_exp(FL, Timeout), m_exps(FL, Body)};
m_exp(FL, {tuple, L, Es}) -> {tuple, FL(L), m_exps(FL, Es)};
m_exp(FL, {'try', L, Body, Cases, Catches, After}) ->
    {'try', FL(L), m_exps(FL, Body), m_case_clauses(FL, Cases),
     lists:map(fun(C) -> m_catch_clause(FL, C) end, Catches), m_exps(FL, After)};
m_exp(FL, {annotate, L, E, T}) -> {annotate, FL(L), m_exp(FL, E), map_locs_ty(FL, T)};
m_exp(FL, {assert, L, E, T}) -> {assert, FL(L), m_exp(FL, E), map_locs_ty(FL, T)}.

-spec m_exp_bin_elem(loc_fun(), ast:exp_bitstring_elem()) -> ast:exp_bitstring_elem().
m_exp_bin_elem(FL, {bin_element, L, V, default, Spec}) -> {bin_element, FL(L), m_exp(FL, V), default, Spec};
m_exp_bin_elem(FL, {bin_element, L, V, Size, Spec}) ->
    {bin_element, FL(L), m_exp(FL, V), m_exp(FL, Size), Spec}.

-spec m_map_assocs(loc_fun(), [ast:map_assoc()]) -> [ast:map_assoc()].
m_map_assocs(FL, Assocs) -> lists:map(fun(A) -> m_map_assoc(FL, A) end, Assocs).

-spec m_map_assoc(loc_fun(), ast:map_assoc()) -> ast:map_assoc().
m_map_assoc(FL, A = {map_field_opt, _, _, _}) -> m_map_assoc_opt(FL, A);
m_map_assoc(FL, {map_field_req, L, K, V}) -> {map_field_req, FL(L), m_exp(FL, K), m_exp(FL, V)}.

-spec m_map_assoc_opt(loc_fun(), ast:map_assoc_opt()) -> ast:map_assoc_opt().
m_map_assoc_opt(FL, {map_field_opt, L, K, V}) -> {map_field_opt, FL(L), m_exp(FL, K), m_exp(FL, V)}.

-spec m_qualifiers(loc_fun(), [ast:qualifier()]) -> [ast:qualifier()].
m_qualifiers(FL, Qs) -> lists:map(fun(Q) -> m_qualifier(FL, Q) end, Qs).

-spec m_qualifier(loc_fun(), ast:qualifier()) -> ast:qualifier().
m_qualifier(FL, Q = {zip, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {generate, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {generate_strict, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {b_generate, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {b_generate_strict, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {m_generate, _, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, Q = {m_generate_strict, _, _, _, _}) -> m_generator(FL, Q);
m_qualifier(FL, E) -> m_exp(FL, E).

-spec m_generator(loc_fun(), ast:generators()) -> ast:generators().
m_generator(FL, {zip, L, Gens}) -> {zip, FL(L), lists:map(fun(G) -> m_generator(FL, G) end, Gens)};
m_generator(FL, {generate, L, P, E}) -> {generate, FL(L), m_pat(FL, P), m_exp(FL, E)};
m_generator(FL, {generate_strict, L, P, E}) -> {generate_strict, FL(L), m_pat(FL, P), m_exp(FL, E)};
m_generator(FL, {b_generate, L, P, E}) -> {b_generate, FL(L), m_pat(FL, P), m_exp(FL, E)};
m_generator(FL, {b_generate_strict, L, P, E}) -> {b_generate_strict, FL(L), m_pat(FL, P), m_exp(FL, E)};
m_generator(FL, {m_generate, L, K, V, E}) -> {m_generate, FL(L), m_pat(FL, K), m_pat(FL, V), m_exp(FL, E)};
m_generator(FL, {m_generate_strict, L, K, V, E}) ->
    {m_generate_strict, FL(L), m_pat(FL, K), m_pat(FL, V), m_exp(FL, E)}.

-spec m_pats(loc_fun(), [ast:pat()]) -> [ast:pat()].
m_pats(FL, Ps) -> lists:map(fun(P) -> m_pat(FL, P) end, Ps).

-spec m_pat(loc_fun(), ast:pat()) -> ast:pat().
m_pat(FL, {atom, L, A}) -> {atom, FL(L), A};
m_pat(FL, {char, L, C}) -> {char, FL(L), C};
m_pat(FL, {float, L, F}) -> {float, FL(L), F};
m_pat(FL, {integer, L, I}) -> {integer, FL(L), I};
m_pat(FL, {string, L, S}) -> {string, FL(L), S};
m_pat(FL, {nil, L}) -> {nil, FL(L)};
m_pat(FL, {wildcard, L}) -> {wildcard, FL(L)};
m_pat(FL, {var, L, Ref}) -> {var, FL(L), Ref};
m_pat(FL, {bin, L, Elems}) -> {bin, FL(L), lists:map(fun(El) -> m_pat_bin_elem(FL, El) end, Elems)};
m_pat(FL, {match, L, P1, P2}) -> {match, FL(L), m_pat(FL, P1), m_pat(FL, P2)};
m_pat(FL, {cons, L, Hd, Tl}) -> {cons, FL(L), m_pat(FL, Hd), m_pat(FL, Tl)};
m_pat(FL, {op, L, Op, Args}) -> {op, FL(L), Op, m_pats(FL, Args)};
m_pat(FL, {map, L, Assocs}) ->
    {map, FL(L),
     lists:map(fun({map_field_req, AL, K, V}) -> {map_field_req, FL(AL), m_pat(FL, K), m_pat(FL, V)} end,
               Assocs)};
m_pat(FL, {tuple, L, Ps}) -> {tuple, FL(L), m_pats(FL, Ps)}.

-spec m_pat_bin_elem(loc_fun(), ast:pat_bitstring_elem()) -> ast:pat_bitstring_elem().
m_pat_bin_elem(FL, {bin_element, L, V, default, Spec}) -> {bin_element, FL(L), m_pat(FL, V), default, Spec};
m_pat_bin_elem(FL, {bin_element, L, V, Size, Spec}) ->
    {bin_element, FL(L), m_pat(FL, V), m_exp(FL, Size), Spec}.

-spec m_guards(loc_fun(), [ast:guard()]) -> [ast:guard()].
m_guards(FL, Guards) -> lists:map(fun(G) -> m_guard_tests(FL, G) end, Guards).

-spec m_guard_tests(loc_fun(), [ast:guard_test()]) -> [ast:guard_test()].
m_guard_tests(FL, Ts) -> lists:map(fun(T) -> m_guard_test(FL, T) end, Ts).

-spec m_guard_test(loc_fun(), ast:guard_test()) -> ast:guard_test().
m_guard_test(FL, {atom, L, A}) -> {atom, FL(L), A};
m_guard_test(FL, {char, L, C}) -> {char, FL(L), C};
m_guard_test(FL, {float, L, F}) -> {float, FL(L), F};
m_guard_test(FL, {integer, L, I}) -> {integer, FL(L), I};
m_guard_test(FL, {string, L, S}) -> {string, FL(L), S};
m_guard_test(FL, {nil, L}) -> {nil, FL(L)};
m_guard_test(FL, {var, L, Ref}) -> {var, FL(L), Ref};
m_guard_test(FL, {bin, L, Elems}) ->
    {bin, FL(L), lists:map(fun(El) -> m_guard_bin_elem(FL, El) end, Elems)};
m_guard_test(FL, {cons, L, Hd, Tl}) -> {cons, FL(L), m_guard_test(FL, Hd), m_guard_test(FL, Tl)};
m_guard_test(FL, {call, L, F, Args}) -> {call, FL(L), m_guard_test(FL, F), m_guard_tests(FL, Args)};
m_guard_test(FL, {call_remote, L, M, F, Args}) ->
    {call_remote, FL(L), m_guard_test(FL, M), m_guard_test(FL, F), m_guard_tests(FL, Args)};
m_guard_test(FL, {map_create, L, Assocs}) ->
    {map_create, FL(L), lists:map(fun(A) -> m_map_assoc_opt(FL, A) end, Assocs)};
m_guard_test(FL, {map_update, L, T, Assocs}) ->
    {map_update, FL(L), m_guard_test(FL, T), m_map_assocs(FL, Assocs)};
m_guard_test(FL, {op, L, Op, A, B}) -> {op, FL(L), Op, m_guard_test(FL, A), m_guard_test(FL, B)};
m_guard_test(FL, {op, L, Op, A}) -> {op, FL(L), Op, m_guard_test(FL, A)};
m_guard_test(FL, {tuple, L, Ts}) -> {tuple, FL(L), m_guard_tests(FL, Ts)}.

-spec m_guard_bin_elem(loc_fun(), external_types:bin_elem(ast:guard_test(), ast:guard_test())) ->
    external_types:bin_elem(ast:guard_test(), ast:guard_test()).
m_guard_bin_elem(FL, {bin_element, L, V, default, Spec}) ->
    {bin_element, FL(L), m_guard_test(FL, V), default, Spec};
m_guard_bin_elem(FL, {bin_element, L, V, Size, Spec}) ->
    {bin_element, FL(L), m_guard_test(FL, V), m_guard_test(FL, Size), Spec}.
