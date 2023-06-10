-module(ast_utils_tests).

-include_lib("eunit/include/eunit.hrl").

export_modules_test() ->
    RawForms = parse:parse_file_or_die("./test_files/export_modules/module1.erl"),
    Forms = ast_transform:trans("./test_files/export_modules/module1.erl", RawForms),
    [module2, module3] = ast_utils:export_modules(Forms).
