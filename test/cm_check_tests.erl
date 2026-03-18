-module(cm_check_tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

% A project in a temporary directory with main.erl as its only entry point, checked
% several times while its files and the options change.

-define(_timeout(E), {timeout, 45, fun() -> E end}).

-define(MAIN, "-module(main).\n-export([f/0, g/0]).\n-spec f() -> integer().\n-spec g() -> integer().\n").
-define(HELPER, "-module(helper).\n-compile([export_all, nowarn_export_all]).\n").

-spec with_project(fun((file:name()) -> ok)) -> ok.
with_project(Action) ->
    tmp:with_tmp_dir("cm_check", "root", delete,
        fun(Dir) ->
            utils:mkdirs(filename:join(Dir, "_build/default/lib")),
            write(Dir, "rebar.lock", ""),
            write(Dir, "main.erl", ?MAIN ++ "f() -> 1.\ng() -> 2.\n"),
            Action(Dir)
        end).

-spec write(file:name(), file:name(), string()) -> ok.
write(Dir, Name, Content) -> ok = file:write_file(filename:join(Dir, Name), Content).

-spec opts(file:name()) -> #opts{}.
opts(Dir) ->
    #opts{files = [filename:join(Dir, "main.erl")], project_root = Dir, mode = test_mode, report_mode = report}.

% what was checked, with the base names of the files
-spec check(#opts{}) -> cm_check:check_list().
check(Opts) ->
    lists:sort([{filename:basename(F), Funs} || {F, Funs} <- etylizer_main:doWork(Opts)]).

% In report mode a failed function is not checked again: its report is stored. In
% early-exit mode it is checked again and fails.
stored_report_test_() ->
    ?_timeout(with_project(fun(Dir) ->
        Opts = opts(Dir),
        write(Dir, "main.erl", ?MAIN ++ "f() -> 1.\ng() -> not_an_integer.\n"),
        ?assertEqual([{"main.erl", all}], check(Opts)),
        ?assertEqual([], check(Opts)),
        Index = cm_index:load_index(paths:rebar_lock_file(Opts), none, paths:index_file_name(Opts), test_mode),
        [{{g, 0}, Report}] = cm_index:reports(filename:join(Dir, "main.erl"), Index),
        ?assertEqual("Error: main:g/0", string:slice(Report, 0, 15)),
        ?assertThrow({etylizer, ty_error, _}, check(Opts#opts{report_mode = early_exit})),
        write(Dir, "main.erl", ?MAIN ++ "f() -> 1.\ng() -> 3.\n"),
        ?assertEqual([{"main.erl", [{g, 0}]}], check(Opts)),
        ?assertEqual([], cm_index:reports(filename:join(Dir, "main.erl"),
            cm_index:load_index(paths:rebar_lock_file(Opts), none, paths:index_file_name(Opts), test_mode)))
    end)).

% A function that was not checked because of -o is checked by the next run without it.
only_test_() ->
    ?_timeout(with_project(fun(Dir) ->
        Opts = opts(Dir),
        ?assertEqual([{"main.erl", [{f, 0}]}], check(Opts#opts{type_check_only = ["main:f/0"]})),
        ?assertEqual([], check(Opts#opts{type_check_only = ["main:f/0"]})),
        ?assertEqual([{"main.erl", [{g, 0}]}], check(Opts)),
        ?assertEqual([], check(Opts))
    end)).

% A changed function that is ignored with -i is checked by the next run without it.
ignore_test_() ->
    ?_timeout(with_project(fun(Dir) ->
        Opts = opts(Dir),
        ?assertEqual([{"main.erl", all}], check(Opts)),
        write(Dir, "main.erl", ?MAIN ++ "f() -> 3.\ng() -> 4.\n"),
        ?assertEqual([{"main.erl", [{f, 0}]}], check(Opts#opts{type_check_ignore = ["main:g/0"]})),
        ?assertEqual([{"main.erl", [{g, 0}]}], check(Opts)),
        ?assertEqual([], check(Opts))
    end)).

% The callers of a function that is gone are checked again, also without an export list.
removed_function_test_() ->
    ?_timeout(with_project(fun(Dir) ->
        Opts = opts(Dir),
        write(Dir, "main.erl", ?MAIN ++ "f() -> helper:a().\ng() -> helper:b().\n"),
        write(Dir, "helper.erl", ?HELPER ++ "-spec a() -> integer().\na() -> 1.\n-spec b() -> integer().\nb() -> 2.\n"),
        ?assertEqual([{"helper.erl", all}, {"main.erl", all}], check(Opts)),
        write(Dir, "helper.erl", ?HELPER ++ "-spec b() -> integer().\nb() -> 2.\n"),
        ?assertEqual([{"main.erl", [{f, 0}]}], check(Opts))
    end)).

% Other options: everything is checked again.
changed_options_test_() ->
    ?_timeout(with_project(fun(Dir) ->
        Opts = opts(Dir),
        ?assertEqual([{"main.erl", all}], check(Opts)),
        ?assertEqual([], check(Opts)),
        ?assertEqual([{"main.erl", all}], check(Opts#opts{no_exhaustiveness = ["f/0"]})),
        ?assertEqual([], check(Opts#opts{no_exhaustiveness = ["f/0"]}))
    end)).
