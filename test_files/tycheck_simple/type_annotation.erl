-module(type_annotation).

-compile(export_all).
-compile(nowarn_export_all).

-include("etylizer.hrl").

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% TYPE ANNOTATIONS    %%%%%%%%%%%%%%%%%%%%%%%%
 
% user-defined type
-spec annot_01() -> atom().
annot_01() -> ?annotate_type(foobar, atom()).

-spec annot_02(integer()) -> any().
annot_02(N) -> ?annotate_type(N, number()).

-spec annot_03_fail(integer()) -> atom().
annot_03_fail(N) -> ?annotate_type(N, atom()).

-type annot_user_04() :: {foo}.
-spec annot_04({foo}) -> {foo}.
annot_04(N) -> ?annotate_type(N, annot_user_04()).

-spec annot_05_fail(integer()) -> atom().
annot_05_fail(N) -> ?annotate_type(N, pos_integer()).

-spec assert_01() -> atom().
assert_01() ->
    X = {a, b},
    % does not fail as type of X is inferred to be 
    % {a | b} U atom()
    ?assert_type(X, atom()). 

-spec assert_02_fail() -> {a, b}.
assert_02_fail() ->
    X = {a, b},
    ?assert_type(X, atom()). 

-spec assert_03_fail() -> {foo, bar}.
assert_03_fail() ->
    X = {a, b},
    % fails because return type atom() does not match spec {foo, bar}
    ?assert_type(X, atom()).

-spec assert_04(term()) -> atom().
assert_04(N) -> ?assert_type(N, atom()). % downcast

% check 0 branches for redundancy???
-spec to_upper([byte()]) -> Result when Result :: [byte()] ; (char()) -> char().
%-spec to_upper([byte()]) -> [byte()] ; (char()) -> char().
to_upper(_) -> error(impl).
-spec assert_05() -> nonempty_string().
assert_05() ->
    to_upper(?assert_type("FOO", [byte()])).

-spec assert_06(integer(), tuple()) -> [integer()].
assert_06(V, Graph) ->
    ?assert_type(element(?assert_type(V + 1, pos_integer()), Graph), [integer()]).

%%%%%%%%%%%%%%%%%%%%%%%% PATTERN ASSERTIONS  %%%%%%%%%%%%%%%%%%%%%%%%

-spec assert_pattern_01({ok, foo|hello}) -> {ok, atom()}.
assert_pattern_01(Z) ->
    ?assert_pattern({ok, foo}, Z).

-spec assert_pattern_02_fail({ok, foo}) -> {ok, atom()}.
assert_pattern_02_fail(Z) ->
    ?assert_pattern({ok, foo}, Z). % we can't make something exhaustive if it's already exhaustive

-spec assert_pattern_03(ok | error) -> ok.
assert_pattern_03(X) ->
    ?assert_pattern(ok, X).

-spec assert_pattern_04({ok | foo, atom()}) -> {ok, atom()}.
assert_pattern_04(Z) ->
    {ok, Val} = ?assert_pattern({ok, _}, Z),
    {ok, Val}.
