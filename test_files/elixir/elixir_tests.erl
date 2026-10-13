-module(elixir_tests).

% The modules of test_files/elixir/*.ex, checked like test_files/tycheck_simple.
% Needs Elixir's lib directory in ERL_LIBS (make elixir-tests).

-include_lib("eunit/include/eunit.hrl").
-include("etylizer_main.hrl").

elixir_test_() ->
    {ok, _} = application:ensure_all_started(elixir),
    tmp:with_tmp_dir("elixir_tests", "ebin", delete,
        fun(Dir) ->
            Sources = [list_to_binary(F) || F <- filelib:wildcard("test_files/elixir/*.ex")],
            {ok, _, _} = 'Elixir.Kernel.ParallelCompiler':compile_to_path(Sources, list_to_binary(Dir)),
            parse_cache:with_cache(#opts{}, fun() ->
                tycheck_simple_tests:check_decls_in_files(filelib:wildcard(Dir ++ "/*.beam"), all, sets:new())
            end)
        end).
