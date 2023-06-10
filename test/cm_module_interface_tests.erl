-module(cm_module_interface_tests).

-include_lib("eunit/include/eunit.hrl").

extract_interface_test() ->
    TestFilePath = "./test_files/extract_interface_test.erl",
    RawForms = parse:parse_file_or_die(TestFilePath),
    Forms = ast_transform:trans(TestFilePath, RawForms),

    Interface = ast_utils:extract_interface_declaration(Forms),

    verify_contains_function(exported_function, Interface),

    verify_contains_type(exported_type_1, Interface),
    verify_contains_type(exported_type_2, Interface),
    verify_contains_type(local_type_1, Interface),
    verify_contains_type(local_type_2, Interface),

    verify_does_not_contain_function(local_function, Interface),

    verify_does_not_contain_type(local_type_3, Interface).

verify_contains_type(TypeName, Forms) ->
    Result = utils:everything(
               fun(T) ->
                       case T of
                           {attribute, _, type, _, {Name, _}} ->
                               case Name == TypeName of
                                   false -> error;
                                   _ -> {ok, T}
                               end;
                           _ -> error
                       end
               end, Forms),
    true = Result =/= [].

verify_does_not_contain_type(TypeName, Forms) ->
    Result = utils:everything(
               fun(T) ->
                       case T of
                           {attribute, _, type, _, {Name, _}} ->
                               case Name == TypeName of
                                   false -> error;
                                   _ -> {ok, T}
                               end;
                           _ -> error
                       end
               end, Forms),
    true = Result == [].

verify_contains_function(FunctionName, Forms) ->
    Result = utils:everything(
               fun(T) ->
                       case T of
                           {attribute, _, spec, Name, _, _, _} ->
                               case Name == FunctionName of
                                   false -> error;
                                   _ -> {ok, T}
                               end;
                           _ -> error
                       end
               end, Forms),
    true = Result =/= [].

verify_does_not_contain_function(FunctionName, Forms) ->
    Result = utils:everything(
               fun(T) ->
                       case T of
                           {attribute, _, spec, Name, _, _, _} ->
                               case Name == FunctionName of
                                   false -> error;
                                   _ -> {ok, T}
                               end;
                           _ -> error
                       end
               end, Forms),
    true = Result == [].
