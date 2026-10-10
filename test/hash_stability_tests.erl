-module(hash_stability_tests).

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").
-include("parse.hrl").
-include("cm_fun_deps.hrl").

% @doc Parse a file through the full pipeline (parse + AST transform) without parse cache.
-spec parse_to_internal(file:filename()) -> ast:forms().
parse_to_internal(File) ->
    RawForms = parse:parse_file_or_die(File, #parse_opts{includes = ["src"]}),
    ast_transform:trans(File, RawForms, full).

% @doc Compute per-function body and spec hashes for all functions in a file.
-spec compute_hashes(ast:forms()) -> #{{atom(), arity()} => {string(), string()}}.
compute_hashes(Forms) ->
    #module_info{funs = Funs} = cm_fun_deps:analyze_module(foo, Forms),
    maps:map(fun(_, #fun_info{body_hash = B, spec_hash = S}) -> {B, S} end, Funs).

% @doc Compare hashes between two versions of a file and return functions with changed hashes.
-spec changed_funs(file:filename(), file:filename()) -> [{atom(), arity(), body | spec | both}].
changed_funs(V1File, V2File) ->
    V1Forms = parse_to_internal(V1File),
    V2Forms = parse_to_internal(V2File),
    V1Hashes = compute_hashes(V1Forms),
    V2Hashes = compute_hashes(V2Forms),
    AllKeys = lists:usort(maps:keys(V1Hashes) ++ maps:keys(V2Hashes)),
    lists:filtermap(fun(Key) ->
        {Name, Arity} = Key,
        V1Entry = maps:get(Key, V1Hashes, {"", ""}),
        V2Entry = maps:get(Key, V2Hashes, {"", ""}),
        {V1Body, V1Spec} = V1Entry,
        {V2Body, V2Spec} = V2Entry,
        BodyChanged = V1Body =/= V2Body,
        SpecChanged = V1Spec =/= V2Spec,
        case {BodyChanged, SpecChanged} of
            {false, false} -> false;
            {true, false} -> {true, {Name, Arity, body}};
            {false, true} -> {true, {Name, Arity, spec}};
            {true, true} -> {true, {Name, Arity, both}}
        end
    end, AllKeys).

% Test: modifying f1's body (adding lines) must not change f2/f3's body hashes.
line_shift_hash_stability_test() ->
    Changed = changed_funs(
        "test_files/recompilation/body_change_hash_stable/foo_V1.erl",
        "test_files/recompilation/body_change_hash_stable/foo_V2.erl"),
    % Only f1 should have changed body hash, not f2 and f3
    ?assertEqual([{f1, 0, body}], Changed).

% Test: the log macros expand ?FILE and ?LINE, which shift when lines are added above.
log_macro_hash_stability_test() ->
    Changed = changed_funs(
        "test_files/recompilation/log_macro_hash_stable/foo_V1.erl",
        "test_files/recompilation/log_macro_hash_stable/foo_V2.erl"),
    ?assertEqual([{f1, 0, body}], Changed).

% Test: parsing the same file twice must produce identical body hashes. The variables
% generated for a multi-clause function must be deterministic.
dispatch_var_hash_stability_test() ->
    File = "test_files/recompilation/dispatch_hash_stable/foo.erl",
    Hashes1 = compute_hashes(parse_to_internal(File)),
    Hashes2 = compute_hashes(parse_to_internal(File)),
    ?assertEqual(Hashes1, Hashes2).
