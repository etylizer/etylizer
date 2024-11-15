-module(cm_module_interface).

% @doc This module contains the functionality to retrieve the complete exported
% interface of a module. This includes types that are not exported but referenced
% by other exported types or functions.

-export([extract_interface_declaration/1]).

%% Extracts interface declarations from the given abstract syntax tree (AST) forms.
%% The function takes a list of forms representing the AST of an Erlang module as input
%% and returns a list of forms containing only the exported function and type declarations.
%% It considers all types, exported or not, and only includes the ones that are either exported
%% or are used in the function signatures or exported types.
-spec extract_interface_declaration(ast:forms()) -> ast:forms().
extract_interface_declaration(Forms) ->
    AllTypes = utils:everything(
                 fun(T) ->
                          case T of
                              {attribute, _, type, _, {_Name, _Arity}} -> {ok, T};
                              _ -> error
                          end
                 end, Forms),

    {ExportedFunctions, ExportedTypes} = extract_exported_functions_and_types(Forms),

    NotExportedTypes = lists:filter(
                         fun({attribute, _, type, _, {Name, {ty_scheme, VariableList, _}}}) ->
                                 not sets:is_element({Name, length(VariableList)}, ExportedTypes)
                         end, AllTypes),

    TypesFromExportedTypes = extract_types_from_exported_types(Forms, NotExportedTypes, ExportedTypes),
    TypesFromSignatures = extract_types_from_function_signatures(Forms, NotExportedTypes, ExportedFunctions),

    RelevantTypes = sets:union([ExportedTypes, TypesFromExportedTypes, TypesFromSignatures]),
    Result = utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, spec, Name, Arity, _, _} ->
                      case sets:is_element({Name, Arity}, ExportedFunctions) of
                          true -> {ok, T};
                          false -> error
                      end;
                  {attribute, _, type, _, {Name, {ty_scheme, VariableList, _}}} ->
                      case sets:is_element({Name, length(VariableList)}, RelevantTypes) of
                          true -> {ok, T};
                          false -> error
                      end;
                  _ -> error
              end
      end, Forms),
    ast_utils:remove_locs(Result).

-spec extract_exported_functions_and_types(ast:forms()) -> {sets:set(ast:fun_with_arity()), sets:set(ast:ty_with_arity())}.
extract_exported_functions_and_types(Forms) ->
    Functions = utils:everything(
                  fun(T) ->
                          case T of
                              {attribute, _, export, Functions} -> {ok, Functions};
                              _ -> error
                          end
                  end, Forms),
    Types = utils:everything(
              fun(T) ->
                      case T of
                          {attribute, _, export_type, Types} -> {ok, Types};
                          _ -> error
                      end
              end, Forms),
    {sets:from_list(lists:flatten(Functions)), sets:from_list(lists:flatten(Types))}.

%% Extracts and aggregates types with their arities from exported type declarations in the AST
%% of an Erlang module.
-spec extract_types_from_exported_types(ast:forms(), [ast:type_decl()], sets:set(ast:ty_with_arity())) -> sets:set(ast:ty_with_arity()).
extract_types_from_exported_types(Forms, TypeDeclarations, ExportedTypes) ->
    TySchemes = find_ty_schemes_from_types(Forms, ExportedTypes),
    NamedReferences = utils:everything(
      fun(T) ->
              case T of
                  {named, _, {ty_ref, _, _, _}, _} ->
                      {ok, T};
                  _ ->
                      error
              end
      end, TySchemes),
    traverse_named_references(NamedReferences, TypeDeclarations, sets:new()).

-spec find_ty_schemes_from_types(ast:forms(), sets:set(ast:ty_with_arity())) -> [ast:ty_scheme()].
find_ty_schemes_from_types(Forms, ExportedTypes) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, type, _, {TypeName, TyScheme}} ->
                      {ty_scheme, VariableList, _} = TyScheme,
                      case sets:is_element({TypeName, length(VariableList)}, ExportedTypes) of
                          true -> {ok, TyScheme};
                          false -> error
                      end;
                  _ -> error
              end
      end, Forms).

%% Extracts and aggregates types with their arities from exported function specifications in the AST
%% of an Erlang module.
-spec extract_types_from_function_signatures(ast:forms(), [ast:type_decl()], sets:set(ast:fun_with_arity())) -> sets:set(ast:ty_with_arity()).
extract_types_from_function_signatures(Forms, NotExportedTypes, Functions) ->
    TySchemes = find_ty_schemes_from_functions(Forms, Functions),
    lists:foldl(
      fun handle_function_signature/2,
      sets:new(),
      [{FunctionSignature, NotExportedTypes} || {ty_scheme, _, FunctionSignature} <- TySchemes]).

-spec find_ty_schemes_from_functions(ast:forms(), sets:set(ast:fun_with_arity())) -> [ast:ty_scheme()].
find_ty_schemes_from_functions(Forms, Functions) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, spec, Name, Arity, TyScheme, _} ->
                      case sets:is_element({Name, Arity}, Functions) of
                          true -> {ok, TyScheme};
                          false -> error
                      end;
                  _ -> error
              end
      end, Forms).

-spec handle_function_signature({ast:ty(), [ast:type_decl()]}, sets:set(ast:ty_with_arity())) -> sets:set(ast:ty_with_arity()).
handle_function_signature({{fun_full, Params, ReturnType}, NotExportedTypes}, AccTypes) ->
    NamedReferences = filter_named_references(Params ++ [ReturnType]),
    handle_named_references(NamedReferences, NotExportedTypes, AccTypes);

handle_function_signature({{fun_any_arg, _, ReturnType}, NotExportedTypes}, AccTypes) ->
    NamedReferences = filter_named_references([ReturnType]),
    handle_named_references(NamedReferences, NotExportedTypes, AccTypes);

handle_function_signature(_, AccTypes) ->
    AccTypes.

-spec handle_named_references([ast:ty_named()], [ast:type_decl()], sets:set(ast:ty_with_arity())) -> sets:set(ast:ty_with_arity()).
handle_named_references(NamedReferences, NotExportedTypes, AccTypes) ->
    sets:union(AccTypes, traverse_named_references(NamedReferences, NotExportedTypes, sets:new())).

-spec filter_named_references([ast:ty()]) -> [ast:ty_named()].
filter_named_references(Types) ->
    [Ty || Ty <- Types, is_named_reference(Ty)].

-spec is_named_reference(ast:ty_named()) -> boolean().
is_named_reference({named, _, {ty_ref, _, _, _}, _}) ->
    true;
is_named_reference(_) ->
    false.

%% Recursively traverses and collects tuples {Name, Arity} of type references from a list of named type references.
%% The function stops traversing when it has gone through all the type references and returns a set of
%% tuples representing the types in the form {Name, Arity}. It also takes care of cyclic type definitions by filtering out names
%% that have already been added to the list.
-spec traverse_named_references([ast:ty_named()], [ast:type_decl()], sets:set(ast:ty_with_arity())) -> sets:set(ast:ty_with_arity()).
traverse_named_references([], _, Types) ->
    Types;

traverse_named_references([CurrentReference | RemainingReferences], TypeDeclarations, Types) ->
    {named, _, {ty_ref, _, CurrentName, TypeArity}, ParameterTypes} = CurrentReference,
    CurrentType = {CurrentName, TypeArity},
    NextReferences = case find_type_declaration(CurrentType, TypeDeclarations) of
                         {value, TyDecl} -> find_named_references(TyDecl);
                         false -> []
                     end,
    ParameterReferences = handle_parameter_types(ParameterTypes),
    % Filter out existing Names from the NextReferences list to prevent infinite loops
    % when we encounter cyclic type definitions.
    FilteredNextReferences = lists:filter(fun({named, _, {ty_ref, _ModName, Name, Arity}, _}) ->
                                                  not sets:is_element({Name, Arity}, Types)
                                          end, NextReferences ++ ParameterReferences),
    traverse_named_references(RemainingReferences ++ FilteredNextReferences, TypeDeclarations, sets:add_element(CurrentType, Types)).

-spec find_type_declaration(ast:ty_with_arity(), [ast:type_decl()]) -> {value, ast:type_decl()} | false.
find_type_declaration({TypeName, TypeArity}, TypeDeclarations) ->
    lists:search(
      fun({attribute, _, type, _, {Name, {ty_scheme, VariableList, _}}}) ->
              Name == TypeName andalso TypeArity == length(VariableList)
      end, TypeDeclarations).

-spec handle_parameter_types([ast:ty()]) -> [ast:ty_named()].
handle_parameter_types(ParameterTypes) ->
    References = handle_parameter_types_internal(ParameterTypes, sets:new()),
    sets:to_list(References).

-spec handle_parameter_types_internal([ast:ty()], sets:set(ast:ty_named())) -> sets:set(ast:ty_named()).
handle_parameter_types_internal([Head | Tail], References) ->
    case Head of
        {named, _, _, _, _} -> handle_parameter_types_internal(Tail, sets:add_element(Head, References));
        _ -> handle_parameter_types_internal(Tail, References)
    end;

handle_parameter_types_internal([], References) ->
    References.

-spec find_named_references(ast:type_decl()) -> [ast:ty_named()].
find_named_references(TypeDeclaration) ->
    utils:everything(
      fun(T) ->
              case T of
                  {named, _, {ty_ref, _Mod, _Name, _}, _} -> {ok, T};
                  _ -> error
              end
      end, TypeDeclaration).
