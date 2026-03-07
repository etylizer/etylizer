-module(tuples).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

%%%%%%%%%%%%%%%%%%%%%%%% TUPLES %%%%%%%%%%%%%%%%%%%%%%%

-spec tuple_01() -> {integer(), string()}.
tuple_01() -> {42, "foo"}.

-spec tuple_02_fail() -> {integer(), string()}.
tuple_02_fail() -> {"foo", 42}.

-spec tuple_03() -> {atom(), integer(), {boolean(), string()}}.
tuple_03() -> {foo, 42, {true, "foo"}}.

-spec tuple_04({atom(), integer()}) -> integer().
tuple_04(X) ->
    case X of
        {_, I} -> I
    end.

-spec tuple_05_fail({atom(), integer()}) -> integer().
tuple_05_fail(X) ->
    case X of
        {A, _} -> A
    end.

-spec tuple_06(_, _) -> ok | nok.
tuple_06(X, X) -> ok;
tuple_06(_, _) -> nok.

% #260
-spec tuple_07(tuple()) -> ok.
tuple_07(T) when is_tuple(T) -> ok.

-type tlist(E) :: nil | {E, tlist(E)}.
-type tnonempty_list(E) :: {E, tlist(E)}.
-spec list_as_tuple_01_fail(tnonempty_list(integer())) -> integer().
list_as_tuple_01_fail(L) ->
    case L of
        {_, nil} -> 2; % [_] :: single-element list
        {_, A} ->      % [_ | A] ::  rest
          case A of
            nil -> 3; % redundant, already checked for nil
            _   -> 4 
          end
    end.

% inference test
-spec list_as_tuple_02() -> tlist(integer()).
list_as_tuple_02() ->
    {1, nil}.

-spec list_as_tuple_03_fail() -> tlist(integer()).
list_as_tuple_03_fail() ->
    {1, 1}.

% example from ordsets
% is_set
-spec list_as_tuple_05(tlist(term()), term()) -> boolean().
list_as_tuple_05({E2, Es}, E1) when E1 < E2 -> list_as_tuple_05(Es, E2);
list_as_tuple_05({_, _}, _) -> false;
list_as_tuple_05(nil, _) -> true.

-spec list_as_tuple_06_fail(term()) -> boolean().
list_as_tuple_06_fail({E, Es}) -> list_as_tuple_05(Es, E); % list_as_tuple_05 is not defined for improper lists
list_as_tuple_06_fail({}) -> true;
list_as_tuple_06_fail(_) -> false.

-spec list_as_tuple_07_h(tnonempty_list(_)) -> integer().
list_as_tuple_07_h({_ , _}) -> 42.

-spec list_as_tuple_07_fail() -> integer().
list_as_tuple_07_fail() -> 
  Fun = fun _F({_, Vs}) -> list_as_tuple_07_h(Vs) end,
  Fun({x, nil}).

% lc_16: filter+extract from a tlist
-spec list_as_tuple_09(tlist({f, a} | b)) -> tlist(a).
list_as_tuple_09(nil) -> nil;
list_as_tuple_09({{f, A}, Rest}) -> {A, list_as_tuple_09(Rest)};
list_as_tuple_09({_, Rest}) -> list_as_tuple_09(Rest).

% identity map over tlist
-spec list_as_tuple_10(tlist(boolean())) -> tlist(boolean()).
list_as_tuple_10(nil) -> nil;
list_as_tuple_10({X, Rest}) -> {X, list_as_tuple_10(Rest)}.

-spec list_as_tuple_12(etylizer:mu(nil | {boolean(), etylizer:mu_var()})) -> etylizer:mu(nil | {boolean(), etylizer:mu_var()}).
list_as_tuple_12(nil) -> nil;
list_as_tuple_12({X, Rest}) -> {X, list_as_tuple_12(Rest)}.

-spec list_as_tuple_08(tlist(V)) -> {ok, V} | error | error2.
list_as_tuple_08(nil) -> error;
list_as_tuple_08({V, nil}) -> {ok, V};
list_as_tuple_08({_ , Rest}) ->
    case list_as_tuple_08(Rest) of
        {ok, _} -> error2;
        _ -> error
    end.

-spec list_as_tuple_rep_01(tlist(b)) -> tlist(a).
list_as_tuple_rep_01({_, Rest}) -> {a, list_as_tuple_rep_01(Rest)};
list_as_tuple_rep_01(nil) -> nil.

-spec list_as_tuple_rep_02(etylizer:mu(nil | {b, etylizer:mu_var()})) -> etylizer:mu(nil | {a, etylizer:mu_var()}).
list_as_tuple_rep_02({_, Rest}) -> {a, list_as_tuple_rep_02(Rest)};
list_as_tuple_rep_02(_) -> nil.
