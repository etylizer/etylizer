-module(cm_module_interface_tests).

-include_lib("eunit/include/eunit.hrl").

exported_vs_local_test() ->
    Interface = load_interface("./test_files/extract_interface/exported_vs_local.erl"),

    verify_contains_function(exported_function, 1, Interface),
    verify_does_not_contain_function(local_function, 1, Interface),

    verify_contains_type(exported_type, 0, Interface),
    verify_does_not_contain_type(local_type, 0, Interface).

cyclic_types_test() ->
    Interface = load_interface("./test_files/extract_interface/cyclic_definitions.erl"),

    verify_contains_type(foo, 0, Interface).

transitive_types_test() ->
    Interface = load_interface("./test_files/extract_interface/transitive_type.erl"),

    verify_contains_type(exported_type, 0, Interface),
    verify_contains_type(local_type_1, 0, Interface),
    verify_contains_type(local_type_2, 0, Interface).

parametrized_types_test() ->
    Interface = load_interface("./test_files/extract_interface/m_parametrized_types.erl"),
    verify_contains_function(exported_function, 1, Interface),
    verify_contains_type(parametrized_type, 1, Interface),
    verify_contains_type(parameter_type, 0, Interface).

overloaded_functions_test() ->
    Interface = load_interface("./test_files/extract_interface/overloaded_functions.erl"),

    verify_contains_type(foo, 1, Interface),
    verify_contains_type(foo, 2, Interface),

    verify_does_not_contain_type(foo, 3, Interface),

    verify_contains_function(exported_function, 1, Interface),
    verify_contains_function(exported_function, 2, Interface),

    verify_does_not_contain_function(exported_function, 3, Interface).

no_change_test() ->
    Interface1 = load_interface("./test_files/extract_interface/no_change1.erl"),
    Interface2 = load_interface("./test_files/extract_interface/no_change2.erl"),
    ?assertEqual(Interface1, Interface2).

-spec load_interface(file:filename()) -> ast:forms().
load_interface(Path) ->
    RawForms = parse:parse_file_or_die(Path),
    Forms = ast_transform:trans(Path, RawForms),

    cm_module_interface:extract_interface_declaration(Forms).

-spec verify_contains_type(atom(), integer(), ast:forms()) -> boolean().
verify_contains_type(TypeName, TypeArity, Forms) ->
    TypeDefinition = find_type_definition(TypeName, TypeArity, Forms),
    true = TypeDefinition =/= [].

-spec verify_does_not_contain_type(atom(), integer(), ast:forms()) -> boolean().
verify_does_not_contain_type(TypeName, TypeArity, Forms) ->
    TypeDefinition = find_type_definition(TypeName, TypeArity, Forms),
    true = TypeDefinition == [].

-spec verify_contains_function(atom(), integer(), ast:forms()) -> boolean().
verify_contains_function(FunctionName, FunctionArity, Forms) ->
    Result = find_function_spec(FunctionName, FunctionArity, Forms),
    true = Result =/= [].

-spec verify_does_not_contain_function(atom(), integer(), ast:forms()) -> boolean().
verify_does_not_contain_function(FunctionName, FunctionArity, Forms) ->
    Result = find_function_spec(FunctionName, FunctionArity, Forms),
    true = Result == [].

-spec find_type_definition(atom(), integer(), ast:forms()) -> any(). %TODO return type should be: ast:fun_spec()?
find_type_definition(TypeName, TypeArity, Forms) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, type, _, {Name, {ty_scheme, VariableList, _}}}
                    when Name == TypeName, TypeArity == length(VariableList)
                         -> {ok, T};
                  _ -> error
              end
      end, Forms).

-spec find_function_spec(atom(), integer(), ast:forms()) -> any(). %TODO return type should be: ast:fun_spec()?
find_function_spec(FunctionName, FunctionArity, Forms) ->
    utils:everything(
      fun(T) ->
              case T of
                  {attribute, _, spec, Name, Arity, _, _}
                    when Name == FunctionName, Arity == FunctionArity
                         -> {ok, T};
                  _ -> error
              end
      end, Forms).
