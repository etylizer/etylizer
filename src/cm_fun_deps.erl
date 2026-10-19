-module(cm_fun_deps).

% function-level analysis for incremental type checking 

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
        body_hash = hash({Args, Body}),
        spec_hash = hash_spec(Name, Arity, Forms),
        calls = calls(ModName, Body)
    }.

-spec calls(atom(), ast:exps()) -> [fun_id()].
calls(ModName, Body) ->
    lists:usort(utils:everything(
        fun({ref, Name, Arity}) when is_atom(Name), is_integer(Arity) ->
                {ok, {ModName, Name, Arity}};
           ({qref, Mod, Name, Arity}) when is_atom(Mod), is_atom(Name), is_integer(Arity) ->
                {ok, {Mod, Name, Arity}};
           (_) -> error
        end, Body)).

-spec hash_spec(atom(), arity(), ast:forms()) -> string() | no_spec.
hash_spec(Name, Arity, Forms) ->
    case [S || S = {attribute, _, spec, N, A, _, _} <- Forms, N =:= Name, A =:= Arity] of
        [] -> no_spec;
        [Spec | _] -> hash(Spec)
    end.

-spec hash_decls(ast:forms()) -> string().
hash_decls(Forms) ->
    hash(lists:filter(
        fun({function, _, _, _, _, _}) -> false;
           ({attribute, _, spec, _, _, _, _}) -> false;
           (_) -> true
        end, Forms)).

% location-independent AST hash 
-spec hash(term()) -> string().
hash(Term) ->
    utils:hash_sha1(?assert_type(io_lib:write(ast_utils:remove_locs(Term)), iodata())).
