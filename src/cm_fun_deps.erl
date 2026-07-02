-module(cm_fun_deps).

% @doc This module handles function-level analysis for incremental type checking.
% It extracts per-function info from parsed forms (body hash, spec hash, called functions,
% referenced types) and supports building function-level dependency graphs.

-export([
    analyze_module/2,
    extract_fun_refs/2,
    extract_type_refs/2,
    hash_fun_body/1,
    hash_fun_spec/3,
    hash_module_decls/1
]).

-export_type([
    fun_id/0,
    fun_info/0,
    module_info/0
]).

-include("log.hrl").
-include("etylizer.hrl").

-type fun_id() :: {Module :: atom(), Name :: atom(), Arity :: arity()}.

-type fun_info() :: #{
    body_hash := string(),
    spec_hash := string(),
    calls := [fun_id()],
    type_refs := [atom()]
}.

-type module_info() :: #{
    decls_hash := string(),
    funs := #{fun_id() => fun_info()}
}.

% @doc Extract function-level info from parsed forms.
-spec analyze_module(atom(), ast:forms()) -> module_info().
analyze_module(ModName, Forms) ->
    DeclsHash = hash_module_decls(Forms),
    FunDecls = [F || F = {function, _, _, _, _} <- Forms],
    Funs = lists:foldl(
        fun(FunDecl, Acc) ->
            analyze_fun(ModName, FunDecl, Forms, Acc)
        end, ?assert_type(maps:new(), #{fun_id() => fun_info()}), FunDecls),
    ?assert_type(#{decls_hash => DeclsHash, funs => Funs}, module_info()).

% @doc Analyze a single function declaration.
-spec analyze_fun(atom(), ast:fun_decl(), ast:forms(), #{fun_id() => fun_info()}) ->
    #{fun_id() => fun_info()}.
analyze_fun(ModName, {function, _, Name, Arity, _Clauses} = FunDecl, Forms, Acc) ->
    FunId = {ModName, Name, Arity},
    Info = ?assert_type(#{
        body_hash => hash_fun_body(FunDecl),
        spec_hash => hash_fun_spec(Name, Arity, Forms),
        calls => extract_fun_refs(ModName, FunDecl),
        type_refs => extract_type_refs(FunDecl, Forms)
    }, fun_info()),
    maps:put(FunId, Info, Acc).

% @doc Extract all function references from a function declaration.
% Walks the function body collecting {ref, Name, Arity} and {qref, Mod, Name, Arity} patterns.
-spec extract_fun_refs(atom(), ast:fun_decl()) -> [fun_id()].
extract_fun_refs(ModName, {function, _, _, _, Clauses}) ->
    Refs = utils:everything(
        fun(T) ->
            case T of
                {call, _, {var, _, {ref, Name, Arity}}, _} when is_atom(Name), is_integer(Arity) ->
                    {ok, {ModName, Name, Arity}};
                {call, _, {var, _, {qref, Mod, Name, Arity}}, _} when is_atom(Mod), is_atom(Name), is_integer(Arity) ->
                    {ok, {Mod, Name, Arity}};
                {fun_ref, _, {ref, Name, Arity}} when is_atom(Name), is_integer(Arity) ->
                    {ok, {ModName, Name, Arity}};
                {fun_ref, _, {qref, Mod, Name, Arity}} when is_atom(Mod), is_atom(Name), is_integer(Arity) ->
                    {ok, {Mod, Name, Arity}};
                _ -> error
            end
        end, Clauses),
    lists:uniq(Refs).

% @doc Extract type references from a function declaration and its spec.
-spec extract_type_refs(ast:fun_decl(), ast:forms()) -> [atom()].
extract_type_refs({function, _, Name, Arity, Clauses}, Forms) ->
    Spec = find_spec(Name, Arity, Forms),
    BodyRefs = extract_type_names(Clauses),
    SpecRefs = case Spec of
        none -> [];
        {ok, SpecForm} -> extract_type_names(SpecForm)
    end,
    lists:uniq(BodyRefs ++ SpecRefs).

% @doc Hash a single function body (clauses only, locations and macro artifacts stripped).
-spec hash_fun_body(ast:fun_decl()) -> string().
hash_fun_body({function, _, _, _, Clauses}) ->
    Stripped = normalize_for_hash(Clauses),
    Written = ?assert_type(io_lib:write(Stripped), iodata()),
    utils:hash_sha1(Written).

% @doc Hash a single function spec. Returns "" if no spec exists.
-spec hash_fun_spec(atom(), arity(), ast:forms()) -> string().
hash_fun_spec(Name, Arity, Forms) ->
    case find_spec(Name, Arity, Forms) of
        none -> "";
        {ok, SpecForm} ->
            Stripped = ast_utils:remove_locs(SpecForm),
            Written = ?assert_type(io_lib:write(Stripped), iodata()),
            utils:hash_sha1(Written)
    end.

% @doc Hash module-level declarations (types, records, exports).
-spec hash_module_decls(ast:forms()) -> string().
hash_module_decls(Forms) ->
    Decls = lists:filter(
        fun(Form) ->
            case Form of
                {attribute, _, type, _, _} -> true;
                {attribute, _, record, _} -> true;
                {attribute, _, export, _} -> true;
                {attribute, _, export_type, _} -> true;
                {attribute, _, import, _} -> true;
                _ -> false
            end
        end, Forms),
    Stripped = ast_utils:remove_locs(Decls),
    Written = ?assert_type(io_lib:write(Stripped), iodata()),
    utils:hash_sha1(Written).

% @doc Find the spec form for a function.
-spec find_spec(atom(), arity(), ast:forms()) -> none | {ok, ast:fun_spec()}.
find_spec(Name, Arity, Forms) ->
    case lists:search(
        fun(Form) ->
            case Form of
                {attribute, _, spec, N, A, _, _} -> N =:= Name andalso A =:= Arity;
                _ -> false
            end
        end, Forms) of
        {value, SpecForm} -> {ok, ?assert_type(SpecForm, ast:fun_spec())};
        false -> none
    end.

% @doc Normalize AST for stable hashing: strip locations and replace ?FILE/?LINE
% arguments in log:macro_log calls with constants. The ?FILE and ?LINE macros expand
% to literal values that change when lines are added/removed elsewhere in the file,
% causing false hash changes in unmodified functions.
-spec normalize_for_hash(dynamic()) -> dynamic().
normalize_for_hash(Term) ->
    Normalized = utils:everywhere(fun normalize_macro_args/1, Term),
    ast_utils:remove_locs(Normalized).

% @doc Replace ?FILE and ?LINE arguments in log:macro_log/5 calls with constants.
-spec normalize_macro_args(dynamic()) -> {ok, dynamic()} | error.
normalize_macro_args({call, Loc, {var, VLoc, {qref, log, macro_log, 5}},
                      [_File, _Line, Level, Fmt, Args]}) ->
    {ok, {call, Loc, {var, VLoc, {qref, log, macro_log, 5}},
          [{string, {loc, "", 0, 0}, ""},
           {integer, {loc, "", 0, 0}, 0},
           Level, Fmt, Args]}};
normalize_macro_args(_) -> error.

% @doc Extract type names referenced in a term (by traversing for ty_ref and ty_qref).
-spec extract_type_names(term()) -> [atom()].
extract_type_names(Term) ->
    Refs = utils:everything(
        fun(T) ->
            case T of
                {ty_ref, _, Name, _} when is_atom(Name) -> {ok, Name};
                {named, _, {ty_ref, _, Name, _}, _} when is_atom(Name) -> {ok, Name};
                _ -> error
            end
        end, Term),
    lists:uniq(Refs).
