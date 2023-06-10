-module(cm_module_interface).

% @doc This module contains the functionality to retrieve the complete exported
% interface of a module. This includes types that are not exported but referenced
% by other exported types or functions.

-export([extract_interface_declaration/1]).

-spec extract_interface_declaration(ast:forms()) -> ast:forms().
extract_interface_declaration(Forms) ->
    {ExportedFunctionNames, ExportedTypeNames} = extract_exported_names(Forms),
    AllTypes = utils:everything(
                 fun(T) ->
                          case T of
                              {attribute, _, type, _, {Name, _Arity}} -> {ok, Name};
                              _ -> error
                          end
                 end, Forms),

    AllTypeNamesSet = sets:from_list(AllTypes),
    ExportedTypeNamesSet = sets:from_list(ExportedTypeNames),
    NotExportedTypesSet = sets:subtract(AllTypeNamesSet, ExportedTypeNamesSet),

    NotExportedTypes = sets:to_list(NotExportedTypesSet),

    TypeNamesFromExportedTypes = extract_type_names_from_types(Forms, NotExportedTypes, ExportedTypeNames),
    TypeNamesFromSignatures = extract_type_names_from_function_signatures(Forms, NotExportedTypes, ExportedFunctionNames),
    AllTypeNames = lists:uniq(ExportedTypeNames ++ TypeNamesFromSignatures ++ TypeNamesFromExportedTypes),
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, spec, Name, _, _, _} ->
                      case lists:search(fun(S) -> S == Name end, ExportedFunctionNames) of
                          false -> error;
                          _ -> {ok, T}
                      end;
                  {attribute, _, type, _, {Name, _}} ->
                      case lists:search(fun(S) -> S == Name end, AllTypeNames) of
                          false -> error;
                          _ -> {ok, T}
                      end;
                  _ -> error
              end
      end, Forms).

-spec extract_exported_names(ast:forms()) -> {[atom()], [atom()]}.
extract_exported_names(Forms) ->
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
    FunctionNames = case Functions == [] of
                        false -> lists:map(fun({Name, _}) -> Name end, lists:flatten(Functions));
                        true -> []
                    end,
    TypeNames = case Types == [] of
                    false -> lists:map(fun({Name, _}) -> Name end, lists:flatten(Types));
                    true -> []
                end,
    {FunctionNames, TypeNames}.

-spec extract_type_names_from_types(ast:forms(), [ast:type_decl()], [atom()]) -> [atom()].
extract_type_names_from_types(Forms, TypeDeclarations, TypeNames) ->
    TySchemes = find_ty_schemes_from_type_names(Forms, TypeNames),
    NamedReferences = utils:everything(
      fun(T) ->
              case T of
                  {named, _, {ref, _Name, _}, _} ->
                      {ok, T};
                  _ ->
                      error
              end
      end, TySchemes),
    traverse_named_references(NamedReferences, TypeDeclarations, []).

-spec find_ty_schemes_from_type_names(ast:forms(), [atom()]) -> [ast:ty_scheme()].
find_ty_schemes_from_type_names(Forms, Names) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, type, _, {TypeName, TyScheme}} ->
                      case lists:search(fun(S) -> S == TypeName end, Names) of
                          false -> error;
                          _ -> {ok, TyScheme}
                      end;
                  _ -> error
              end
      end, Forms).

-spec extract_type_names_from_function_signatures(ast:forms(), [ast:type_decl()], [atom()]) -> [atom()].
extract_type_names_from_function_signatures(Forms, NotExportedTypes, FunctionNames) ->
    TySchemes = find_ty_schemes_from_function_names(Forms, FunctionNames),
    lists:foldl(
      fun({ty_scheme, _, FunctionSignature}, AccList) ->
              case FunctionSignature of
                  {fun_full, Params, ReturnType} ->
                      NamedReferences = lists:filter(
                                          fun(Ty) ->
                                                  case Ty of
                                                      {named, _, {ref, _Name, _}, _} -> true;
                                                      _ -> false
                                                  end
                                          end, Params ++ [ReturnType]),
                      AccList ++ traverse_named_references(NamedReferences, NotExportedTypes, []);
                  {fun_any_arg, _, ReturnType} ->
                      case ReturnType of
                          {named, _, {ref, _Name, _}, _} ->
                              AccList ++ traverse_named_references([ReturnType], NotExportedTypes, []);
                          _ ->
                              ok
                      end;
                  {fun_simple, _, _} ->
                      AccList
              end
      end, [], TySchemes).

-spec find_ty_schemes_from_function_names(ast:forms(), [atom()]) -> [ast:ty_scheme()].
find_ty_schemes_from_function_names(Forms, Names) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, spec, FunctionName, _, TyScheme, _} ->
                      case lists:search(fun(S) -> S == FunctionName end, Names) of
                          false -> error;
                          _ -> {ok, TyScheme}
                      end;
                  _ -> error
              end
      end, Forms).

-spec traverse_named_references([ast:ty_named()], [ast:type_decl()], [atom()]) -> [atom()].
traverse_named_references([], _, NameList) ->
    NameList;

traverse_named_references([CurrentReference | RemainingReferences], TypeDeclarations, NameList) ->
    {named, _, {ref, CurrentName, _}, _} = CurrentReference,
    NextReferences = case find_type_declaration(CurrentName, TypeDeclarations) of
                         {ok, TyDecl} -> find_named_references(TyDecl);
                         false -> []
                     end,
    % Filter out existing Names from the NextReferences list to prevent infinite loops
    % when we encounter cyclic type definitions.
    FilteredNextReferences = lists:filter(fun({named, _, {ref, Name, _}, _}) ->
                                                  not lists:member(Name, NameList)
                                          end, NextReferences),
    traverse_named_references(RemainingReferences ++ FilteredNextReferences, TypeDeclarations, [CurrentName | NameList]).


-spec find_type_declaration(atom(), [ast:type_decl()]) -> {ok, ast:type_decl()} | false.
find_type_declaration(TypeName, TypeDeclarations) ->
    case lists:search(fun({attribute, _, type, _, {Name, _}}) -> Name == TypeName end, TypeDeclarations) of
        {value, TypeDeclaration} ->
            {ok, TypeDeclaration};
        false ->
            false
    end.

-spec find_named_references(ast:type_decl()) -> [ast:ty_named()].
find_named_references(TypeDeclaration) ->
    utils:everything(
      fun(T) ->
              case T of
                  {named, _, {ref, _Name, _}, _} -> {ok, T};
                  _ -> error
              end
      end, TypeDeclaration).
