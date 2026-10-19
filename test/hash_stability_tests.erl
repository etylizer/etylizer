-module(hash_stability_tests).

-include_lib("eunit/include/eunit.hrl").
-include("parse.hrl").
-include("cm_fun_deps.hrl").

% parses without parse cache.
-spec analyze(file:filename()) -> #{{atom(), arity()} => #fun_info{}}.
analyze(File) ->
    RawForms = parse:parse_file_or_die(File, #parse_opts{includes = ["src"]}),
    #module_info{funs = Funs} = cm_fun_deps:analyze_module(foo, ast_transform:trans(File, RawForms, full)),
    Funs.

hash_stability_test() ->
    Dir = "test_files/recompilation/body_change_hash_stable/",
    V1 = analyze(Dir ++ "foo_V1.erl"),
    V2 = analyze(Dir ++ "foo_V2.erl"),
    ?assertEqual([{f1, 0}], [F || F <- lists:sort(maps:keys(V1)), maps:get(F, V1) =/= maps:get(F, V2)]).
