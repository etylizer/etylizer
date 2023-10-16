-module(test_utils).

% @doc Extracts tests from files. A test file is an .erl file containing lines of the
% form %-ety({test, good}) or %-ety({test, bad, "..."). A single test starts with the line
% after such a declaration and extends until the next test declaration or eof.
% A file without any test declarations implicitly carries the declaration %-ety({test, good})
% before the first line.

-include_lib("eunit/include/eunit.hrl").
-include_lib("log.hrl").

-export([
    extract_tests/1,
    is_equiv/2,
    is_subtype/2
]).

-export_type([
    test_result/0, test_spec/0
]).

-type test_result() :: good | {bad, string()}.
-type test_spec() :: {test_result(), Lineno::integer(), [ast_erl:form()]}.

-spec form_lineno(ast_erl:form()) -> integer().
form_lineno(F) ->
    case F of
        {attribute, {L, _}, _, _} -> L;
        {function, {L, _}, _, _, _} -> L;
        {eof, {L, _}} -> L
    end.

-spec extract_tests([{t:lineno(), test_result()}, ...], [ast_erl:form()]) -> [test_spec()].
extract_tests(LinenoAndResults, Forms) ->
    case LinenoAndResults of
        [{N, R} | RestSpecs] ->
            Forms1 = lists:dropwhile(fun (F) -> form_lineno(F) =< N end, Forms),
            case RestSpecs of
                [] -> [{R, N, Forms1}];
                [{N1, _} | _] ->
                    {Forms2, RestForms} =
                        lists:splitwith(fun (F) -> form_lineno(F) < N1 end, Forms1),
                    RestResult = extract_tests(RestSpecs, RestForms),
                    [{R, N, Forms2} | RestResult]
            end
    end.

-spec extract_tests(file:filename()) -> [test_spec()].
extract_tests(Path) ->
    RawForms = parse:parse_file_or_die(Path),
    case attr:ety_attrs_from_file(Path) of
        {error, Msg} -> throw({invalid_testfile, Msg});
        {ok, AllAttrs} ->
            LinenoAndResults = lists:filtermap(fun (A) ->
                case A of
                    {ety, {loc, _, N, _}, Test} ->
                        case Test of
                            {test, good} -> {true, {N, good}};
                            {test, bad, Msg} -> {true, {N, {bad, Msg}}};
                            _ -> false
                        end;
                    _ -> false
                end end, AllAttrs),
            ?LOG_DEBUG("AllAttrs = ~1000p~nLinenoAndResults = ~1000p", AllAttrs, LinenoAndResults),
            case LinenoAndResults of
                [] -> [{good, 0, RawForms}]; % no test spec -> single test
                _ -> extract_tests(LinenoAndResults, RawForms)
            end
    end.

-spec extract_tests_test() -> ok.
extract_tests_test() ->
    Ts = extract_tests("test_files/test_utils_test.erl"),
    ?LOG_DEBUG("Ts = ~1000p", Ts),
    case Ts of
        [
            {{bad, "Blub"}, 6, [{function, _, foo, 1, _}, {function, _, bar, 1, _}]},
            {good, 11, [{function, _, spam, 1, _}, {eof, _}]}
        ] -> ok;
        _ ->
            io:format("Unexpected test: ~100p", [Ts]),
            ?assert(false)
    end.

-spec is_equiv(ast:ty(), ast:ty()) -> boolean().
is_equiv(S, T) ->
    Symtab = symtab:empty(),
    subty:is_subty(Symtab, S, T) andalso
        subty:is_subty(Symtab, T, S).

-spec is_subtype(ast:ty(), ast:ty()) -> boolean().
is_subtype(S, T) ->
    Symtab = symtab:empty(),
    subty:is_subty(Symtab, S, T).
