-module(index_tests).

-include_lib("eunit/include/eunit.hrl").

has_file_changed_test() ->
    prepare_test_file(),

    TestFilePath = "./test_files/index/test/module.erl",
    RawForms = parse:parse_file_or_die(TestFilePath),
    Forms = ast_transform:trans(TestFilePath, RawForms),

    Index = index:put_into_index(TestFilePath, Forms, maps:new()),

    swap_test_files(),

    true = index:has_file_changed(TestFilePath, Index),

    clean_up_test_file().

has_exported_interface_changed_test() ->
    prepare_test_file(),

    TestFilePath = "./test_files/index/test/module.erl",
    RawForms = parse:parse_file_or_die(TestFilePath),
    Forms = ast_transform:trans(TestFilePath, RawForms),

    Index = index:put_into_index(TestFilePath, Forms, maps:new()),

    swap_test_files(),

    ChangedRawForms = parse:parse_file_or_die(TestFilePath),
    ChangedForms = ast_transform:trans(TestFilePath, ChangedRawForms),

    true = index:has_exported_interface_changed(TestFilePath, ChangedForms, Index),

    clean_up_test_file().

prepare_test_file() ->
    case filelib:is_file("./test_files/index/test/module.erl") of
       true -> file:delete("./test_files/index/test/module.erl");
       false -> ok
    end,
    file:copy("./test_files/index/original/module.erl", "./test_files/index/test/module.erl").

swap_test_files() ->
    file:delete("./test_files/index/test/module.erl"),
    file:copy("./test_files/index/changed/module.erl", "./test_files/index/test/module.erl").

clean_up_test_file() ->
    file:delete("./test_files/index/test/module.erl").
