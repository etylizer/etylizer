-module(ast_utils).

-export([
    modname_from_path/1,
    remove_locs/1,
    referenced_modules/1,
    referenced_modules_via_types/1,
    referenced_recursive_variables/1,
    unfold_ty/2
]).

-include("etylizer.hrl").

-spec modname_from_path(file:filename()) -> ast:mod_name().
modname_from_path(Path) -> list_to_atom(filename:basename(Path, ".erl")).

-spec loc_replacer(dynamic()) -> {ok, dynamic()} | error.
loc_replacer({loc, _, _, _, _, _}) -> {ok, {loc, "", 0, 0, -1, -1}};
loc_replacer(_) -> error.

-spec remove_locs(dynamic()) -> dynamic().
remove_locs(X) ->
    utils:everywhere(fun loc_replacer/1, X).

-spec referenced_modules_via_types(ast:forms()) -> [ast:mod_name()].
referenced_modules_via_types(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {attribute, _, import, {ModuleName, _}} when is_atom(ModuleName) -> {ok, ModuleName};
                            {ty_qref, ModuleName, _, _} when is_atom(ModuleName) -> {ok, ModuleName};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(?assert_type(Modules, [ast:mod_name()])).

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
    lists:uniq(?assert_type(Modules, [ast:mod_name()])).

-spec referenced_recursive_variables(ast:ty()) -> [ast:ty_mu_var()].
referenced_recursive_variables(Forms) ->
    Modules = utils:everything(
                fun(T) ->
                        case T of
                            {mu_var, Name} when is_atom(Name) -> {ok, {mu_var, Name}};
                            _ -> error
                        end
                end, Forms),
    lists:uniq(?assert_type(Modules, [ast:ty_mu_var()])).

% @doc Unfold a type by resolving all named type references via the symtab.
% Recursive back-references are replaced with {ty_hole}.
-spec unfold_ty(symtab:t(), ast:ty()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, Ty) -> unfold_ty(Tab, Ty, #{}).

-spec unfold_ty_list(symtab:t(), [ast:ty()], map()) -> [ast:ty()].
unfold_ty_list(Tab, Args, Memo) ->
    ?assert_type([unfold_ty(Tab, T, Memo) || T <- Args], [ast:ty()]).

-spec unfold_ty_single(symtab:t(), ast:ty(), map()) -> ast:ty().
unfold_ty_single(Tab, T, Memo) ->
    ?assert_type(unfold_ty(Tab, T, Memo), ast:ty()).

-spec unfold_ty_named(symtab:t(), ast:loc(), ast:ty_ref(), [ast:ty()], map()) -> ast:ty() | {ty_hole}.
unfold_ty_named(_Tab, _Loc, Ref, Args, Memo) when is_map_key({Ref, Args}, Memo) ->
    {ty_hole};
unfold_ty_named(Tab, Loc, Ref, Args, Memo) ->
    {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, Tab),
    Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
    Expanded = subst:apply(Map, Body, no_clean),
    unfold_ty(Tab, Expanded, Memo#{{Ref, Args} => []}).

-spec unfold_ty(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, {named, Loc, Ref, Args}, Memo) ->
    unfold_ty_named(Tab, Loc, Ref, Args, Memo);
unfold_ty(Tab, T, Memo) ->
    unfold_ty_compound_2(Tab, T, Memo).

% Chain of catch-alls: compound 2-elem → compound 3-elem → list-like → leaf
-spec unfold_ty_compound_2(symtab:t(), ast:ty(), map()) -> ast:ty().
unfold_ty_compound_2(Tab, {union, Args}, Memo) ->
    {union, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_compound_2(Tab, {intersection, Args}, Memo) ->
    {intersection, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_compound_2(Tab, {tuple, Args}, Memo) ->
    {tuple, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_compound_2(Tab, {fun_any_arg, Ret}, Memo) ->
    {fun_any_arg, unfold_ty_single(Tab, Ret, Memo)};
unfold_ty_compound_2(Tab, {negation, T}, Memo) ->
    {negation, unfold_ty_single(Tab, T, Memo)};
unfold_ty_compound_2(Tab, T, Memo) ->
    unfold_ty_compound_3(Tab, T, Memo).

-spec unfold_ty_compound_3(symtab:t(), ast:ty(), map()) -> ast:ty().
unfold_ty_compound_3(Tab, {fun_full, Args, Ret}, Memo) ->
    {fun_full, unfold_ty_list(Tab, Args, Memo), unfold_ty_single(Tab, Ret, Memo)};
unfold_ty_compound_3(Tab, {mu, Var, T}, Memo) ->
    {mu, Var, unfold_ty_single(Tab, T, Memo)};
unfold_ty_compound_3(Tab, {map, Assocs}, Memo) ->
    {map, [{Kind, unfold_ty_single(Tab, K, Memo), unfold_ty_single(Tab, V, Memo)} || {Kind, K, V} <- Assocs]};
unfold_ty_compound_3(Tab, T, Memo) ->
    unfold_ty_list_or_leaf(Tab, T, Memo).

-spec unfold_ty_list_or_leaf(symtab:t(), ast:ty(), map()) -> ast:ty().
unfold_ty_list_or_leaf(Tab, {list, T}, Memo) ->
    {list, unfold_ty_single(Tab, T, Memo)};
unfold_ty_list_or_leaf(Tab, {nonempty_list, T}, Memo) ->
    {nonempty_list, unfold_ty_single(Tab, T, Memo)};
unfold_ty_list_or_leaf(Tab, {cons, A, B}, Memo) ->
    {cons, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_list_or_leaf(Tab, {improper_list, A, B}, Memo) ->
    {improper_list, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_list_or_leaf(Tab, {nonempty_improper_list, A, B}, Memo) ->
    {nonempty_improper_list, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_list_or_leaf(_Tab, T, _Memo) -> T.
