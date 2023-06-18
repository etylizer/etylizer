-module(ast_utils_tests).

-include_lib("eunit/include/eunit.hrl").

referenced_modules_test() ->
    Path = "./test_files/referenced_modules/module1.erl",
    RawForms = parse:parse_file_or_die(Path),
    Forms = ast_transform:trans(Path, RawForms),

    Modules = ast_utils:referenced_modules(Forms),
    true = lists:member(module2, Modules),
    true = lists:member(module3, Modules),
    true = lists:member(module4, Modules).
