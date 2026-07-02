-module(test_utils).

% @doc Extracts tests from files. A test file is an .erl file containing lines of the
% form %-etylizer({test, good}) or %-etylizer({test, bad, "..."). A single test starts with the line
% after such a declaration and extends until the next test declaration or eof.
% A file without any test declarations implicitly carries the declaration %-etylizer({test, good})
% before the first line.

-include_lib("eunit/include/eunit.hrl").
-include("log.hrl").

-export([
    extract_tests/1,
    ety_to_cduce_tally/2,
    named/1,
    named/2,
    extend_symtab/2, 
    extend_symtab/3,
    extend_symtabs/2,
    solutions/1,
    test_tally/2, test_tally/3, test_tally/4,
    test_tally_satisfiable/4
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
                    {etylizer, {loc, _, N, _}, Test} ->
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

% translates the etylizer tally input constraints to a cduce tally call
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
to_cduce({list, X}) -> io_lib:format("[(~s)*]", [to_cduce(X)]);
to_cduce({nonempty_list, X}) -> io_lib:format("([(~s)*] \\ [])", [to_cduce(X)]);
to_cduce({empty_list}) -> "[]";
to_cduce({predef, any}) -> "Any";
to_cduce({predef, none}) -> "Empty";
to_cduce({predef, integer}) -> "Int";
% floats are treated to tags in CDuce
to_cduce({predef, float}) -> "`float";
to_cduce({predef_alias, boolean}) -> "Bool";
to_cduce({predef_alias, nonempty_list}) -> "([Any*] \\ [])";
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
to_cduce(_Ast) ->
    errors:not_implemented("Cduce construct not supported").

% we use $ in the variable name which is not a valid character in OCaml
% replace this with some other character
-spec to_var(ast:ty_var()) -> string().
to_var({var, Name}) ->
    "'" ++ 
    string:replace(
    string:replace(
      string:replace(
        string:replace(string:lowercase(erlang:atom_to_list(Name)), "$", "u")
      , "@", "u")
    , "'", "")
    , "'", ""
    ).


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

-type expected_subst() :: {
  #{ atom() => ast:ty() },  % lower bounds
  #{ atom() => ast:ty() } % upper bounds
}.

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst())) -> ok.
test_tally(ConstrList, ExpectedSubst) ->
    test_tally(ConstrList, ExpectedSubst, [], symtab:empty()).

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst()), [ast:ty_varname()]) -> ok.
test_tally(ConstrList, ExpectedSubst, FixedVars) ->
    test_tally(ConstrList, ExpectedSubst, FixedVars, symtab:empty()).

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst()), [ast:ty_varname()], symtab:t()) -> ok.
test_tally(ConstrList, ExpectedSubst, FixedVars, Symtab) ->
  Constrs = sets:from_list(
                lists:map(
                  fun ({T, U}) -> {scsubty, sets:from_list([ast:loc_auto()], [{version, 2}]), T, U} end,
                  ConstrList
                 ), [{version, 2}]),

  Res = tally:tally(Symtab, Constrs, sets:from_list(FixedVars, [{version, 2}])),
  case Res of
    [_ | _] -> 
      ?LOG_WARN("Tally result:~n~s",
        pretty:render_substs(lists:map(fun (S) -> subst:base_subst(S) end, Res))),
      find_subst(ExpectedSubst, Res, Res);
    _ -> 
      case ExpectedSubst of 
        [] -> ok;
        _ -> error(utils:sformat("Unexpected result from tally: ~w", Res))
      end
  end,

  % test satisfiable mode of tally
  test_tally_satisfiable(length(ExpectedSubst) > 0, ConstrList, FixedVars, Symtab),

  ok.

-spec test_tally_satisfiable(boolean(), list({ast:ty(), ast:ty()}), [ast:ty_varname()], symtab:t()) -> ok.
test_tally_satisfiable(Satisfiable, ConstrList, FixedVars, Symtab) ->
  Constrs = sets:from_list(lists:map(
                  fun ({T, U}) -> {scsubty, sets:from_list([ast:loc_auto()]), T, U} end,
                  ConstrList
                 )),

  % test satisfiable mode of tally
  {Satisfiable, _} = tally:is_satisfiable(Symtab, Constrs, sets:from_list(FixedVars)),
  ok.

%% Suppress warnings about unmatched patterns
%% TODO fix this somehow or not...
-dialyzer({no_match, find_subst/3}).
-spec find_subst(list(expected_subst()), [subst:t()], [subst:t()]) -> ok.
find_subst([], [], _) -> ok;
find_subst([{Low, High} | _], [], Sols) ->
  ?LOG_WARN("~nCould not find substitutions among remaining ~p tally solutions for~n" ++
    "expected lower bound:~n~s~n~nexpected upper bound:~n~s~n~nRemaining:~s",
            length(Sols),
            pretty:render_subst(Low),
            pretty:render_subst(High),
            pretty:render_substs(lists:map(fun (S) -> subst:base_subst(S) end, Sols))
  ),
  error("test failed because tally returned no substitution that matches low and high bounds");
find_subst([], [_X | _Xs], Remaining) ->
  Substs = lists:map(fun (S) -> subst:base_subst(S) end, Remaining),
  ?LOG_WARN("~nToo many substitutions return from tally. Unconsumed: ~200p", Substs),
  error("Too many substitutions returned from tally");
find_subst(X = [{Low, High} | OtherTests], [TallySubst | Others], AllTally) ->
  Subst = subst:base_subst(TallySubst),
  Valid = lists:any(
    fun({{Var, LowerBound}, {Var, UpperBound}}) ->
        TyOther = maps:get(Var, Subst, {var, Var}),
        not (subty:is_subty(symtab:empty(), LowerBound, TyOther) andalso
          subty:is_subty(symtab:empty(), TyOther, UpperBound))
    end, lists:zip(lists:sort(maps:to_list(Low)), lists:sort(maps:to_list(High)))),
  case Valid of
    true -> find_subst(X, Others, AllTally);
    false -> find_subst(OtherTests, AllTally -- [TallySubst], AllTally -- [TallySubst])
  end.

solutions(Number) ->
  [{#{}, #{}} || _ <- lists:seq(1, Number)].


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

cduce_translation_test() ->
    {ok, [Cons]} = file:consult("test_files/erlang_types/tally/fun_local_02.config"),
    % should not crash
    _Str = ety_to_cduce_tally(Cons, []),
    ok.

-endif.
