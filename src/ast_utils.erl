-module(ast_utils).

-export([remove_locs/1, export_modules/1, extract_interface_declaration/1]).

-include_lib("log.hrl").

-spec remove_locs(T) -> T.
remove_locs(X) ->
    LocToError = fun(Z) ->
        case Z of
            {loc, _, _, _} -> {ok, {loc, "", 0, 0}};
            _ -> error
        end
    end,
    utils:everywhere(LocToError, X).

-spec export_modules(ast:forms()) -> [atom()].
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

-spec extract_interface_declaration(ast:forms()) -> ast:forms().
extract_interface_declaration(Forms) ->
    {ExportedFunctionNames, ExportedTypeNames} = extract_exported_names(Forms),
    AllTypes = utils:everything(
                 fun(T) ->
                          case T of
                              {attribute, _, type, _, _} -> {ok, T};
                              _ -> error
                          end
                 end, Forms),
    {ExportedTypes, NotExportedTypes} = lists:splitwith(
     fun({attribute, _, type, _, {Name, _}}) ->
             case lists:search(fun(S) -> S == Name end, ExportedTypeNames) of
                 false -> false;
                 _ -> true
             end
     end, AllTypes),
    TypeNamesFromExportedTypes = extract_type_names_from_types(Forms, NotExportedTypes, ExportedTypes),
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

-spec extract_exported_names(ast:forms()) -> tuple().
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
traverse_named_references(NamedReferences, TypeDeclarations, NameList) ->
    case NamedReferences of
        [CurrentReference | RemainingReferences] ->
            {named, _, {ref, CurrentName, _}, _} = CurrentReference,
            TyDecl = find_type_declaration(CurrentName, TypeDeclarations),
            NextReferences = find_named_references(TyDecl),
            traverse_named_references(RemainingReferences ++ NextReferences, TypeDeclarations, [CurrentName | NameList]);
        [] ->
            NameList
    end.

-spec find_type_declaration(atom(), [ast:type_decl()]) -> ast:type_decl().
find_type_declaration(TypeName, TypeDeclarations) ->
    case lists:search(fun({attribute, _, type, _, {Name, _}}) -> Name == TypeName end, TypeDeclarations) of
        {value, TypeDeclaration} ->
            TypeDeclaration;
        false ->
            ?ABORT("Did not find type declaration.")
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
