-module(cm_fun_deps).

% @doc Function-level analysis for incremental type checking: the hashes of the body and
% of the spec of each function, and the functions it calls.

-export([analyze_module/2]).

-export_type([fun_id/0, fun_info/0, module_info/0]).

-include("etylizer.hrl").
-include("cm_fun_deps.hrl").

-type fun_id() :: {Module :: atom(), Name :: atom(), Arity :: arity()}.
-type fun_info() :: #fun_info{}.
-type module_info() :: #module_info{}.

-spec analyze_module(atom(), ast:forms()) -> module_info().
analyze_module(ModName, Forms) ->
    Funs = [{{Name, Arity}, analyze_fun(ModName, F, Forms)}
            || F = {function, _, Name, Arity, _, _} <- Forms],
    #module_info{decls_hash = hash_decls(Forms), funs = maps:from_list(Funs)}.

-spec analyze_fun(atom(), ast:fun_decl(), ast:forms()) -> fun_info().
analyze_fun(ModName, {function, _, Name, Arity, Args, Body}, Forms) ->
    #fun_info{
        body_hash = hash(utils:everywhere(fun normalize_log_call/1, {Args, Body})),
        spec_hash = hash_spec(Name, Arity, Forms),
        calls = calls(ModName, Body)
    }.

% The functions that a function body refers to
-spec calls(atom(), ast:exps()) -> [fun_id()].
calls(ModName, Body) ->
    lists:usort(utils:everything(
        fun({ref, Name, Arity}) when is_atom(Name), is_integer(Arity) ->
                {ok, {ModName, Name, Arity}};
           ({qref, Mod, Name, Arity}) when is_atom(Mod), is_atom(Name), is_integer(Arity) ->
                {ok, {Mod, Name, Arity}};
           (_) -> error
        end, Body)).

-spec hash_spec(atom(), arity(), ast:forms()) -> string().
hash_spec(Name, Arity, Forms) ->
    case [S || S = {attribute, _, spec, N, A, _, _} <- Forms, N =:= Name, A =:= Arity] of
        [] -> "";
        [Spec | _] -> hash(Spec)
    end.

% Any form other than a function or its spec may affect all functions
-spec hash_decls(ast:forms()) -> string().
hash_decls(Forms) ->
    hash(lists:filter(
        fun({function, _, _, _, _, _}) -> false;
           ({attribute, _, spec, _, _, _, _}) -> false;
           (_) -> true
        end, Forms)).

% Hashes a part of the AST, independent of its location in the file
-spec hash(term()) -> string().
hash(Term) ->
    utils:hash(?assert_type(io_lib:write(ast_utils:remove_locs(Term)), iodata())).

% The log macros pass ?FILE and ?LINE, which change when code above the call moves
-spec normalize_log_call(dynamic()) -> {ok, dynamic()} | error.
normalize_log_call({call, Loc, F = {var, _, {qref, log, macro_log, 5}}, [_File, _Line | Args]}) ->
    {ok, {call, Loc, F, Args}};
normalize_log_call(_) -> error.
