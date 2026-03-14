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

-spec loc_replacer(term()) -> {ok, {loc, string(), 0, 0}} | error.
loc_replacer({loc, File, Line, Col}) ->
    case utils:is_string(File) andalso is_integer(Line) andalso is_integer(Col) of
        true -> {ok, {loc, "", 0, 0}};
        false -> error
    end;
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
    ?assert_type(lists:uniq(Modules), [ast:mod_name()]).

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
    ?assert_type(lists:uniq(Modules), [ast:mod_name()]).

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

% @doc Unfold a type by resolving all named type references via the symtab.
% Recursive back-references are replaced with {ty_hole}.
-spec unfold_ty(symtab:t(), ast:ty()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, Ty) -> unfold_ty(Tab, Ty, #{}).

-spec unfold_ty(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty(Tab, {named, Loc, Ref, Args}, Memo) ->
    unfold_ty_named(Tab, Loc, Ref, Args, Memo);
unfold_ty(Tab, Ty, Memo) ->
    unfold_ty_compound_2(Tab, Ty, Memo).

-spec unfold_ty_named(symtab:t(), ast:loc(), ast:ty_ref(), [ast:ty()], map()) -> ast:ty() | {ty_hole}.
unfold_ty_named(Tab, Loc, Ref, Args, Memo) ->
    case Memo of
        #{{Ref, Args} := _} -> {ty_hole};
        _ ->
            {ty_scheme, Vars, Body} = symtab:lookup_ty(Ref, Loc, Tab),
            Map = subst:from_list(lists:zip([V || {V, _Bound} <- Vars], Args)),
            Expanded = subst:apply(Map, Body, no_clean),
            unfold_ty(Tab, Expanded, Memo#{{Ref, Args} => []})
    end.

-spec unfold_ty_compound_2(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty_compound_2(Tab, {fun_full, Args, Ret}, Memo) ->
    {fun_full, unfold_ty_list(Tab, Args, Memo), unfold_ty_single(Tab, Ret, Memo)};
unfold_ty_compound_2(Tab, {fun_any_arg, Ret}, Memo) ->
    {fun_any_arg, unfold_ty_single(Tab, Ret, Memo)};
unfold_ty_compound_2(Tab, {negation, T}, Memo) ->
    {negation, unfold_ty_single(Tab, T, Memo)};
unfold_ty_compound_2(Tab, Ty, Memo) ->
    unfold_ty_compound_3(Tab, Ty, Memo).

-spec unfold_ty_compound_3(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty_compound_3(Tab, {cons, A, B}, Memo) ->
    {cons, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_compound_3(Tab, {improper_list, A, B}, Memo) ->
    {improper_list, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_compound_3(Tab, {nonempty_improper_list, A, B}, Memo) ->
    {nonempty_improper_list, unfold_ty_single(Tab, A, Memo), unfold_ty_single(Tab, B, Memo)};
unfold_ty_compound_3(Tab, Ty, Memo) ->
    unfold_ty_list_or_leaf(Tab, Ty, Memo).

-spec unfold_ty_list_or_leaf(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty_list_or_leaf(Tab, {union, Args}, Memo) ->
    {union, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_list_or_leaf(Tab, {intersection, Args}, Memo) ->
    {intersection, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_list_or_leaf(Tab, {tuple, Args}, Memo) ->
    {tuple, unfold_ty_list(Tab, Args, Memo)};
unfold_ty_list_or_leaf(Tab, {list, T}, Memo) ->
    {list, unfold_ty_single(Tab, T, Memo)};
unfold_ty_list_or_leaf(Tab, {nonempty_list, T}, Memo) ->
    {nonempty_list, unfold_ty_single(Tab, T, Memo)};
unfold_ty_list_or_leaf(Tab, {map, Assocs}, Memo) ->
    {map, [{Kind, unfold_ty_single(Tab, K, Memo), unfold_ty_single(Tab, V, Memo)} || {Kind, K, V} <- Assocs]};
unfold_ty_list_or_leaf(Tab, {mu, Var, T}, Memo) ->
    {mu, Var, unfold_ty_single(Tab, T, Memo)};
unfold_ty_list_or_leaf(_Tab, T, _Memo) -> T.

-spec unfold_ty_list(symtab:t(), [ast:ty()], map()) -> [ast:ty() | {ty_hole}].
unfold_ty_list(Tab, Types, Memo) ->
    [unfold_ty(Tab, T, Memo) || T <- Types].

-spec unfold_ty_single(symtab:t(), ast:ty(), map()) -> ast:ty() | {ty_hole}.
unfold_ty_single(Tab, T, Memo) ->
    unfold_ty(Tab, T, Memo).
