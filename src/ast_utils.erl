-module(ast_utils).

-export([
    modname_from_path/1,
    remove_locs/1,
    referenced_modules/1,
    referenced_modules_via_types/1,
    referenced_recursive_variables/1,
    unfold_ty/2
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

-spec referenced_modules_via_types(ast:forms()) -> [ast:mod_name()].
referenced_modules_via_types(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} -> {ok, ModuleName};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(Modules).

-spec referenced_modules(ast:forms()) -> [ast:mod_name()].
referenced_modules(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} -> {ok, ModuleName};
                            {qref, ModuleName, _, _} -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} -> {ok, ModuleName};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(Modules).

-spec referenced_recursive_variables(ast:ty()) -> [ast:ty_mu_var()].
referenced_recursive_variables(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {mu_var, Name} -> {ok, {mu_var, Name}};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(Modules).

% @doc Unfold a type by resolving all named type references via the symtab.
% Recursive back-references are replaced with {ty_hole}.
-spec unfold_ty(symtab:t(), ast:ty()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, Ty) -> unfold_ty(Tab, Ty, #{}).

-spec unfold_ty(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, {named, Loc, Ref, Args}, Memo) ->
    case Memo of
        #{{Ref, Args} := _} -> {ty_hole};
        _ ->
            {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, Tab),
            Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
            Expanded = subst:apply(Map, Body, no_clean),
            unfold_ty(Tab, Expanded, Memo#{{Ref, Args} => []})
    end;
unfold_ty(Tab, {union, Args}, Memo) ->
    {union, [unfold_ty(Tab, T, Memo) || T <- Args]};
unfold_ty(Tab, {intersection, Args}, Memo) ->
    {intersection, [unfold_ty(Tab, T, Memo) || T <- Args]};
unfold_ty(Tab, {tuple, Args}, Memo) ->
    {tuple, [unfold_ty(Tab, T, Memo) || T <- Args]};
unfold_ty(Tab, {fun_full, Args, Ret}, Memo) ->
    {fun_full, [unfold_ty(Tab, T, Memo) || T <- Args], unfold_ty(Tab, Ret, Memo)};
unfold_ty(Tab, {fun_any_arg, Ret}, Memo) ->
    {fun_any_arg, unfold_ty(Tab, Ret, Memo)};
unfold_ty(Tab, {negation, T}, Memo) ->
    {negation, unfold_ty(Tab, T, Memo)};
unfold_ty(Tab, {list, T}, Memo) ->
    {list, unfold_ty(Tab, T, Memo)};
unfold_ty(Tab, {nonempty_list, T}, Memo) ->
    {nonempty_list, unfold_ty(Tab, T, Memo)};
unfold_ty(Tab, {cons, A, B}, Memo) ->
    {cons, unfold_ty(Tab, A, Memo), unfold_ty(Tab, B, Memo)};
unfold_ty(Tab, {improper_list, A, B}, Memo) ->
    {improper_list, unfold_ty(Tab, A, Memo), unfold_ty(Tab, B, Memo)};
unfold_ty(Tab, {nonempty_improper_list, A, B}, Memo) ->
    {nonempty_improper_list, unfold_ty(Tab, A, Memo), unfold_ty(Tab, B, Memo)};
unfold_ty(Tab, {map, Assocs}, Memo) ->
    {map, [{Kind, unfold_ty(Tab, K, Memo), unfold_ty(Tab, V, Memo)} || {Kind, K, V} <- Assocs]};
unfold_ty(Tab, {mu, Var, T}, Memo) ->
    {mu, Var, unfold_ty(Tab, T, Memo)};
unfold_ty(_Tab, T, _Memo) -> T.
