-module(ast_utils).

-export([remove_locs/1, referenced_modules/1]).

-export_type([ty_module_name/0]).

-type ty_module_name() :: atom().

-spec remove_locs(T) -> T.
remove_locs(X) ->
    LocToError = fun(Z) ->
        case Z of
            {loc, _, _, _} -> {ok, {loc, "", 0, 0}};
            _ -> error
        end
    end,
    utils:everywhere(LocToError, X).

-spec referenced_modules(ast:forms()) -> [ty_module_name()].
referenced_modules(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} -> {ok, ModuleName};
                            {qref, ModuleName, _, _} -> {ok, ModuleName};
                            _ -> error
                        end
                end, Forms),
    utils:list_uniq(Modules).
