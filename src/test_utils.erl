-module(test_utils).

% @doc Extracts tests from files. A test file is an .erl file containing lines of the
% form %-ety({test, good}) or %-ety({test, bad, "..."). A single test starts with the line
% after such a declaration and extends until the next test declaration or eof.
% A file without any test declarations implicitly carries the declaration %-ety({test, good})
% before the first line.

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-export([
    extract_tests/1,
    is_equiv/2,
    is_subtype/2,
    reset_ets/0,
    ety_to_cduce_tally/2,
    format_tally_config/3,
    named/1,
    named/2,
    extend_symtab/2, 
    extend_symtab/3,
    extend_symtabs/2
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
    reset_ets(),
    Symtab = symtab:empty(),
    subty:is_subty(Symtab, S, T) andalso
        subty:is_subty(Symtab, T, S).

-spec is_subtype(ast:ty(), ast:ty()) -> boolean().
is_subtype(S, T) ->
    reset_ets(),
    Symtab = symtab:empty(),
    subty:is_subty(Symtab, S, T).

-spec reset_ets() -> ok.
reset_ets() ->
    ecache:reset_all(),
    ok.

% transforms a tally:tally constraints to a config file which can be loaded in the tally_tests.erl tests
% TODO free variables #74
format_tally_config(Constraints, _FixedVars, Symtab) ->
    "[" ++ lists:join(",", [io_lib:format("{~p, ~p}", [S, T]) || {_, _, S, T} <- Constraints]) ++ "]." 
    ++ "\n" 
    ++ io_lib:format("~p.", [Symtab]).

% translates the ety tally input constraints to a cduce tally call
% not all constructs are supported
% TODO free variables #73
-spec ety_to_cduce_tally(list(constr:simp_constr()) | list({ast:ty(), ast:ty()}), list(ast:ty_varname())) -> string().
ety_to_cduce_tally(Constraints, Order) ->
    VariableOrder = io_lib:format("~s", [lists:join(" ", [to_var({var, V}) || V <- Order])]),
    PairsOfConstraints = lists:map(
        fun
            ({S, T}) -> "\n("++ to_cduce(S) ++ ", "++ to_cduce(T) ++ ")";
            ({csuby, _, S, T}) -> "\n("++ to_cduce(S) ++ ", "++ to_cduce(T) ++ ")"
        end, Constraints),
    "debug tallying ([" ++ VariableOrder ++ "] [] [" ++ PairsOfConstraints ++ "]);;".


-spec to_cduce(ast:ty()) -> string().
to_cduce({predef, any}) -> "Any";
to_cduce({predef, none}) -> "Empty";
to_cduce({predef, integer}) -> "Int";
% floats are treated to tags in CDuce
to_cduce({predef, float}) -> "`float";
to_cduce({predef_alias, non_neg_integer}) -> "(0--*)";
to_cduce({singleton, float}) -> "`float";
to_cduce({mu, _, _}) -> "RECTYPE";
to_cduce({range, X, Y}) -> io_lib:format("(~s--~s)",[erlang:integer_to_list(X), erlang:integer_to_list(Y)]);
to_cduce({singleton, I}) when is_integer(I) -> erlang:integer_to_list(I);
to_cduce({singleton, A}) when is_atom(A) -> io_lib:format("`~s", [erlang:atom_to_list(A)]);
to_cduce({negation, X}) -> io_lib:format("(Any \\ ~s)", [to_cduce(X)]);
to_cduce({tuple, [A, B]}) -> io_lib:format("(~s, ~s)", [to_cduce(A), to_cduce(B)]);
to_cduce({intersection, X}) -> "(" ++ lists:join(" & ", [to_cduce(Z) || Z <- X]) ++ ")";
to_cduce({union, X}) -> "(" ++ lists:join(" | ", [to_cduce(Z) || Z <- X]) ++ ")";
to_cduce({var, Name}) -> to_var({var, Name});
to_cduce({named, _, _, _}) -> "NAMED";
to_cduce({fun_full, [S], T}) -> io_lib:format("(~s -> ~s)", [to_cduce(S), to_cduce(T)]);
to_cduce(Ast) ->
    error({construct_not_supported, Ast}).

% we use $ in the variable name which is not a valid character in OCaml
% replace this with some other character
-spec to_var(ast:ty_var()) -> string().
to_var({var, Name}) ->
    "'" ++ string:replace(erlang:atom_to_list(Name), "$", "u").


named(Ref) ->
    named(Ref, []).

named(Ref, Args) ->
  % Use the dummy '.' file as the module for testing purposes
  {named, ast:loc_auto(), {ty_ref, '.', Ref, length(Args)}, Args}.

extend_symtab(Def, Scheme) ->
  extend_symtab(Def, Scheme, symtab:empty()).

extend_symtab(Def, Scheme, Symtab) ->
  TyDef = {Def, Scheme},
  Form = {attribute, ast:loc_auto(), type, transparent, TyDef},
  symtab:extend_symtab(".", [Form], Symtab, symtab:empty()).

extend_symtabs(DefSchemes, Symtab) ->
  Forms = [{attribute, ast:loc_auto(), type, transparent, TyDef} || TyDef <- DefSchemes],
  symtab:extend_symtab(".", Forms, Symtab, symtab:empty()).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

cduce_translation_test() ->
    test_utils:reset_ets(),
    {ok, [Cons]} = file:consult("test_files/tally/fun_local_02_plus.config"),
    % should not crash
    _Str = ety_to_cduce_tally(Cons, []),
    % io:format(user, "~s~n", [_Str]),
    ok.

-endif.
