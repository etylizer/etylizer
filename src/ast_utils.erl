-module(ast_utils).

-export([
    modname_from_path/1,
    remove_locs/1,
    referenced_modules/1,
    referenced_modules_via_types/1,
    referenced_recursive_variables/1,
    unfold_ty/2,
    unfold_named/4,
    instantiate_scheme/2
]).

-include("etylizer.hrl").

-spec modname_from_path(file:filename()) -> ast:mod_name().
modname_from_path(Path) ->
    Ext = filename:extension(Path),
    list_to_atom(filename:basename(Path, Ext)).

-spec loc_replacer(term()) -> {ok, {loc, string(), 0, 0}} | error.
loc_replacer(X) ->
    case ast:is_loc(X) of
        true -> {ok, {loc, "", 0, 0}};
        false -> error
    end.

-spec remove_locs(dynamic()) -> dynamic().
remove_locs(X) ->
    utils:everywhere(fun loc_replacer/1, X).

-spec referenced_modules_via_types(ast:forms()) -> [ast:mod_name()].
referenced_modules_via_types(Forms) ->
    Modules = ast_traverse:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} -> {ok, ModuleName};
                            _ -> error
                        end
                end, [Forms]),
    lists:uniq(Modules).

-spec referenced_modules(ast:forms()) -> [ast:mod_name()].
referenced_modules(Forms) ->
    Modules = ast_traverse:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} -> {ok, ModuleName};
                            {qref, ModuleName, _, _} -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} -> {ok, ModuleName};
                            _ -> error
                        end
                end, [Forms]),
    lists:uniq(Modules).

-spec referenced_recursive_variables(ast:ty()) -> [ast:ty_mu_var()].
referenced_recursive_variables(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {mu_var, Name} when is_atom(Name) -> {ok, {mu_var, Name}};
                            _ -> error
                        end
                end, Forms),
    ?assert_type(lists:uniq(Modules), [ast:ty_mu_var()]).

% unfold a type by resolving all named type references via the symtab
% recursive back-references are replaced with {ty_hole}
-spec unfold_ty(symtab:t(), ast:ty()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, Ty) -> unfold_ty(Tab, Ty, #{}).

-spec unfold_ty(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, {named, Loc, Ref, Args}, Memo) ->
    case Memo of
        #{{Ref, Args} := _} -> {ty_hole};
        _ ->
            unfold_ty(Tab, unfold_named(Tab, Ref, Args, Loc), Memo#{{Ref, Args} => []})
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

% the body of the named type Ref applied to Args
% fails with a name error at Loc if Ref is not defined
-spec unfold_named(symtab:t(), ast:ty_ref(), [ast:ty()], ast:loc()) -> ast:ty().
unfold_named(Tab, Ref, Args, Loc) ->
    instantiate_scheme(symtab:lookup_ty(Ref, Loc, Tab), Args).

% the body of a type scheme with Args substituted for its parameters
% the bounds of the parameters are ignored
-spec instantiate_scheme(ast:ty_scheme(), [ast:ty()]) -> ast:ty().
instantiate_scheme({ty_scheme, Vars, Body}, Args) ->
    subst:apply(subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)), Body, no_clean).
