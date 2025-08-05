-module(my_and).

-compile(export_all).
-compile(nowarn_export_all).

-include_lib("eunit/include/eunit.hrl").

-spec my_and_infer(any(), T) -> T | false.
my_and_infer(false, _) -> false;
my_and_infer(_, X) -> X.

% from the success typing papers
-spec my_and2_infer(any(), any()) -> boolean().
my_and2_infer(true, true) -> true;
my_and2_infer(_, _) -> false.

% TODO why is this so much slower?
% -spec my_test() -> _.
% my_test() ->
%     ?assertEqual(1, my_and_infer(true, 1)),
%     ?assertEqual("foo", my_and_infer(true, "foo")),
%     ?assertEqual(false, my_and_infer(false, some_atom)),
%     ?assertEqual(false, my_and_infer("bar", false)).

-spec my_1_test() -> _.
my_1_test() ->
    ?assertEqual(1, my_and_infer(true, 1)).

-spec my_2_test() -> _.
my_2_test() ->
    ?assertEqual("foo", my_and_infer(true, "foo")).

-spec my_3_test() -> _.
my_3_test() ->
    ?assertEqual(false, my_and_infer(false, some_atom)).

-spec my_4_test() -> _.
my_4_test() ->
    ?assertEqual(false, my_and_infer("bar", false)).
