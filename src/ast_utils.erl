-module(ast_utils).

-export([remove_locs/1, export_modules/1]).

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

-spec export_modules(ast:forms()) -> [ty_module_name()].
export_modules(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {qref, _, _, _} -> {ok, T};
                            _ -> error
                        end
                end, Forms),
    ModuleList = lists:map(fun({_, ModuleName, _, _}) -> ModuleName end, Modules),
    lists:uniq(ModuleList).
