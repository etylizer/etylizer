-module(erlang_types_test_utils).

-compile([nowarn_export_all, export_all]).

-include_lib("test/erlang_types/erlang_types_test_utils.hrl").
-include("log.hrl").

-type expected_subst() :: {
  #{ atom() => ast:ty() },  % lower bounds
  #{ atom() => ast:ty() } % upper bounds
}.

% creates dummy expected substitutions 
% can be used if only the number of solutions is important,
% not the variable substitutions themselves
-spec solutions(integer()) -> [expected_subst()].
solutions(Number) ->
  [{#{}, #{}} || _ <- lists:seq(1, Number)].

-spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst())) -> _.
test_tally(ConstrList, ExpectedSubst) ->
    test_tally(ConstrList, ExpectedSubst, []).

% -spec test_tally(list({ast:ty(), ast:ty()}), list(expected_subst()), [ast:ty_varname()]) -> _.
test_tally(ConstrList, ExpectedSubst, FixedVars) ->
  test_tally(ConstrList, ExpectedSubst, FixedVars, symtab:empty()).

test_tally(ConstrList, ExpectedSubst, FixedVars, Symtab) ->
  % io:format(user,"Fixed variables: ~p~n", [FixedVars]),
  % test satisfiable mode of tally
  test_tally_satisfiable(length(ExpectedSubst) > 0, ConstrList, FixedVars, Symtab),

  with_symtab(fun() ->
    % test solve mode of tally
    Constrs = 
    sets:from_list( 
      lists:map( 
        fun ({T, U}) -> {scsubty, sets:from_list([loc_auto()]), T, U} end, 
        ConstrList
       )),

    Res = tally:tally(Symtab, Constrs, sets:from_list(FixedVars)),

    case Res of
      [_ | _] -> 
        % ?LOG_WARN("Tally result:~n~s",
        %   pretty:render_substs(lists:map(fun (S) -> subst:base_subst(S) end, Res))),
        find_subst(ExpectedSubst, Res, Res);
      _ -> 
        case ExpectedSubst of 
          [] -> ok;
          _ -> error({"Unexpected result from tally", Res})
        end
    end,

    ok
  end, Symtab).

test_tally_satisfiable(Satisfiable, ConstrList) ->
  test_tally_satisfiable(Satisfiable, ConstrList, [], symtab:empty()).

% -spec test_tally_satisfiable(boolean(), list({ast:ty(), ast:ty()}), [ast:ty_varname()], symtab:t()) -> ok.
test_tally_satisfiable(Satisfiable, ConstrList, FixedVars, Symtab) ->
  with_symtab(fun() ->
    Constrs = 
      sets:from_list(
        lists:map( 
          fun ({T, U}) -> {scsubty, sets:from_list([loc_auto()]), T, U} end,
          ConstrList
      )),

    % test satisfiable mode of tally
    {Satisfiable, _} = tally:is_satisfiable(Symtab, Constrs, sets:from_list(FixedVars)),
    ok
              end,
    Symtab).

% Suppress warnings about unmatched patterns
% TODO fix this somehow or not...
% -dialyzer({no_match, find_subst/3}).
% -spec find_subst(list(expected_subst()), [subst:t()], [subst:t()]) -> ok.
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
find_subst([], [_X | _Xs], _Remaining) ->
  % Substs = lists:map(fun (S) -> subst:base_subst(S) end, Remaining),
  % ?LOG_WARN("~nToo many substitutions return from tally. Unconsumed: ~200p", Substs),
  error("Too many substitutions returned from tally");
find_subst(X = [{Low, High} | OtherTests], [TallySubst | Others], AllTally) ->
  Subst = base_subst(TallySubst),
  Valid = lists:any(
    fun({{Var, LowerBound}, {Var, UpperBound}}) ->
        TyOther = maps:get(Var, Subst, {var, Var}),
        % io:format(user,"Unparsed:~n~p~n", [TyOther]),
        V = ty_parser:parse(TyOther),
        L = ty_parser:parse(LowerBound),
        U = ty_parser:parse(UpperBound),
        not (ty_node:leq(L, V) andalso ty_node:leq(V, U))
        % not (subty:is_subty(symtab:empty(), LowerBound, TyOther) andalso
        %   subty:is_subty(symtab:empty(), TyOther, UpperBound))

    end, lists:zip(lists:sort(maps:to_list(Low)), lists:sort(maps:to_list(High)))),
  case Valid of
    true -> find_subst(X, Others, AllTally);
    false -> find_subst(OtherTests, AllTally -- [TallySubst], AllTally -- [TallySubst])
  end.

base_subst({tally_subst, S, _}) -> S;
base_subst(S) -> S.

loc_auto() -> {loc, "AUTO", -1, -1}.
