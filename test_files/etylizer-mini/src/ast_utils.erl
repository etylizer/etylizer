-module(ast_utils).

-export([
    modname_from_path/1,
    remove_locs/1,
    referenced_modules/1,
    referenced_variables/1
]).

-spec modname_from_path(file:filename()) -> ast:mod_name().
modname_from_path(Path) -> list_to_atom(filename:basename(Path, ".erl")).

-spec remove_locs(T) -> T.
remove_locs(X) ->
    LocToError = fun(Z) ->
        case Z of
            {loc,File,Line,Col} ->
                case utils:is_string(File) andalso is_integer(Line) andalso is_integer(Col) of
                    true -> {ok, {loc, "", 0, 0}};
                    false -> error
                end;
            _ -> error
        end
    end,
    utils:everywhere(LocToError, X).

-spec referenced_modules(ast:forms()) -> [ast:mod_name()].
referenced_modules(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} when is_atom(ModuleName) -> {ok, ModuleName};
                            {qref, ModuleName, _, _} when is_atom(ModuleName) -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} when is_atom(ModuleName) -> {ok, ModuleName};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(Modules).

-spec referenced_variables(ast:ty()) -> [ast:ty_var()].
referenced_variables(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {var, Name} when is_atom(Name) -> {ok, {var, Name}};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(Modules).
