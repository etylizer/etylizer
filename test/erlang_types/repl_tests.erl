-module(repl_tests).

-include_lib("eunit/include/eunit.hrl").

is_empty(String) ->
  {ok, Ty} = repl:parse_raw_type(String),
  global_state:with_new_state(fun() -> repl:is_empty(Ty) end).

parse_raw_type_test() ->
  {ok, {union, [{singleton, gt}, {singleton, lt}]}} =
    repl:parse_raw_type("{union, [{singleton, gt}, {singleton, lt}]}"),
  % optional trailing dot, whitespace and newlines
  {ok, {tuple, [{predef, any}, {var, 'A'}]}} =
    repl:parse_raw_type("  {tuple,\n  [{predef, any}, {var, 'A'}]} . "),
  {ok, {range, '*', 3}} = repl:parse_raw_type("{range, '*', 3}."),
  ok.

parse_raw_type_errors_test() ->
  [{error, _} = repl:parse_raw_type(S) || S <- [
    "",
    "{union, [{singleton, gt}, {singleton, lt}]",
    "{union,, []}",
    "atom()"
  ]].

empty_test() ->
  [{ok, true} = is_empty(S) || S <- [
    "{predef, none}",
    "{union, []}",
    "{intersection, [{singleton, gt}, {singleton, lt}]}",
    "{intersection, [{predef, atom}, {negation, {predef, atom}}]}",
    "{intersection, [{predef_alias, boolean}, {negation, {singleton, true}}, {negation, {singleton, false}}]}",
    "{range, 1, 0}",
    "{tuple, [{predef, none}, {predef, any}]}",
    "{mu, {mu_var, x}, {tuple, [{mu_var, x}]}}"
  ]].

not_empty_test() ->
  [{ok, false} = is_empty(S) || S <- [
    "{predef, any}",
    "{intersection, []}",
    "{union, [{singleton, gt}, {singleton, lt}]}",
    "{singleton, 1}",
    "{var, alpha}",
    "{range, 0, 1}",
    "{fun_full, [{predef, none}], {predef, none}}",
    "{bitstring, 0, 8}",
    "{tuple_any}",
    "{mu, {mu_var, x}, {union, [{empty_list}, {cons, {predef, integer}, {mu_var, x}}]}}"
  ]].

% ty_parser rejects malformed types; later checks must still work
malformed_test() ->
  global_state:with_new_state(fun() ->
    [begin
       {ok, Ty} = repl:parse_raw_type(S),
       {error, _} = repl:is_empty(Ty),
       {ok, false} = repl:is_empty({bitstring, 0, 8})
     end || S <- [
      "{foo, bar}",
      "gt",
      "{named, {loc, \"AUTO\", -1, -1}, {ty_ref, foo, bar, 0}, []}",
      "{mu_var, x}",
      "{mu, {mu_var, x}, {mu_var, x}}"
    ]]
  end).
