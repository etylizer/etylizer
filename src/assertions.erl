-module(assertions).

% etylizer.hrl assertions from outside via position + hash

-export([inject/3]).

-include("etylizer.hrl").

-type pos() :: {Line::integer(), Column::integer()}.
% use only pos() to get the hashes
-type at() :: {Line::integer(), Column::integer(), Hash::string()} | pos().
-type kind() :: assert_type | annotate_type | assert_pattern.
-type wrapper() :: fun((ast_erl:exp()) -> ast_erl:exp()).

% Inject a file holding {assertion, Module, At, Kind, Text, _} assertions.
-spec inject(file:filename(), [ast_erl:form()], file:filename()) -> [ast_erl:form()].
inject(File, Forms, AssertionFile) ->
    Mod = list_to_atom(filename:basename(File, ".erl")),
    {ok, Terms} = ?assert_pattern({ok, _}, file:consult(AssertionFile),
                                  errors:some_error("Cannot read ~s", [AssertionFile])),
    Assertions = ?assert_type([{At, Kind, Text} || {assertion, M, At, Kind, Text, _} <- Terms, M =:= Mod],
                              [{at(), kind(), string()}]),
    lists:foldl(fun(A, Fs) -> assert(File, A, Fs) end, Forms, Assertions).

-spec assert(file:filename(), {at(), kind(), string()}, [ast_erl:form()]) -> [ast_erl:form()].
assert(File, {At, Kind, Text}, Forms) ->
    Pos = {Line, Col} = pos(At),
    {_, Found0} = visit(fun(E, Acc) -> {E, [strip(E) | Acc]} end, Pos, [], Forms),
    Found = lists:usort(Found0),
    [T] = ?assert_pattern([_], [E || E <- Found, {Line, Col, hash(E)} =:= At],
                          errors:some_error("~s:~w:~w: ~w needs the hash of an expression that starts here: ~s",
                                            [File, Line, Col, Kind, render(Found)])),
    W = wrapper(Kind, Text),
    {Forms2, _} = visit(fun(E, Acc) ->
                                case strip(E) =:= T of
                                    true -> {W(E), Acc};
                                    false -> {E, Acc}
                                end
                        end, Pos, [], Forms),
    Forms2.

% The parsed expression is hashed, so its layout in the source does not matter.
-spec hash(ast_erl:exp()) -> string().
hash(E) -> utils:sformat("~6.16.0b", [erlang:phash2(E, 16#1000000)]).

-spec pos(at()) -> pos().
pos({Line, Col}) -> {Line, Col};
pos({Line, Col, _}) -> {Line, Col}.

-spec parse(string()) -> ast_erl:exp().
parse(Text) ->
    {ok, Tokens, _} = ?assert_pattern({ok, _, _}, erl_scan:string(Text ++ "."),
                                      errors:some_error("Cannot parse ~s", [Text])),
    {ok, [E]} = ?assert_pattern({ok, [_]}, erl_parse:parse_exprs(Tokens),
                                errors:some_error("Cannot parse ~s", [Text])),
    ?assert_type(E, ast_erl:exp()).

-spec strip(ast_erl:exp()) -> ast_erl:exp().
strip(E) -> set_anno(erl_anno:new(0), E).

-spec set_anno(ast_erl:anno(), ast_erl:exp()) -> ast_erl:exp().
set_anno(A, E) ->
    ?assert_type(erl_parse:map_anno(fun(_) -> A end, ?assert_type(E, erl_parse:abstract_expr())), ast_erl:exp()).

-spec render([ast_erl:exp()]) -> string().
render([]) -> "none";
render(Es) ->
    string:join([utils:sformat("`~s` (~s)", [erl_pp:expr(?assert_type(E, erl_parse:abstract_expr())), hash(E)])
                 || E <- Es], ", ").

-spec wrapper(kind(), string()) -> wrapper().
wrapper(assert_type, Text) ->
    fun(E) -> A = anno(E), {call, A, {atom, A, ':::'}, [E, {string, A, Text}]} end;
wrapper(annotate_type, Text) ->
    fun(E) -> A = anno(E), {call, A, {atom, A, '::'}, [E, {string, A, Text}]} end;
wrapper(assert_pattern, Text) ->
    Pat0 = parse(Text),
    % the expansion of ?assert_pattern
    Wrap =
        fun(E, A) ->
                Pat = ?assert_type(set_anno(A, Pat0), ast_erl:pat()),
                V = {var, A, 'X__V'},
                Crash = {call, A, {atom, A, error}, [{atom, A, exhaustiveness_violated}]},
                Case = {'case', A, V, [{clause, A, [Pat], [], [V]}, {clause, A, [{var, A, '_'}], [], [Crash]}]},
                {call, A, {'fun', A, {clauses, [{clause, A, [V], [], [Case]}]}}, [E]}
        end,
    % For a match P = E the assertion is about E, so that the position can be the one
    % of a "not all cases are covered" error.
    fun({match, A, P, E}) -> {match, A, P, Wrap(E, A)};
       (E) -> Wrap(E, anno(E))
    end.

-spec anno(ast_erl:exp()) -> ast_erl:anno().
anno(E) -> ?assert_type(element(2, E), ast_erl:anno()).

% Replaces every expression at Pos by what F makes of it, innermost first, threading
% Acc. Only expressions are visited: no patterns, no guards, no function names of calls.
-spec visit(fun((ast_erl:exp(), Acc) -> {ast_erl:exp(), Acc}), pos(), Acc, any()) -> {dynamic(), Acc}.
visit(F, Pos, Acc, Xs) when is_list(Xs) ->
    lists:mapfoldl(fun(X, A) -> visit(F, Pos, A, X) end, Acc, ?assert_type(Xs, [any()]));
visit(_, _, Acc, {attribute, _, _, _} = Form) -> {Form, Acc};
visit(F, Pos, Acc, {clause, A, Ps, Gs, Body}) ->
    {Body2, Acc2} = visit(F, Pos, Acc, Body),
    {{clause, A, Ps, Gs, Body2}, Acc2};
visit(F, Pos, Acc0, T) when is_tuple(T) ->
    Skip = case T of
               {match, _, _, _} -> [3];
               {G, _, _, _} when G =:= generate; G =:= b_generate; G =:= m_generate;
                                 G =:= generate_strict; G =:= b_generate_strict;
                                 G =:= m_generate_strict -> [3];
               {call, _, {atom, _, _}, _} -> [3];
               {call, _, {remote, _, _, _}, _} -> [3];
               _ -> []
           end,
    {Elems, Acc1} = lists:mapfoldl(
                      fun({I, X}, Acc) ->
                              case I =< 2 orelse lists:member(I, Skip) of
                                  true -> {X, Acc};
                                  false when element(1, T) =:= cons, I =:= 4 -> tail(F, Pos, Acc, X);
                                  false -> visit(F, Pos, Acc, X)
                              end
                      end, Acc0, lists:enumerate(tuple_to_list(T))),
    T2 = list_to_tuple(Elems),
    case is_expr(T2) of
        true ->
            E = ?assert_type(T2, ast_erl:exp()),
            case erl_anno:location(anno(E)) =:= Pos of
                true -> F(E, Acc1);
                false -> {T2, Acc1}
            end;
        false -> {T2, Acc1}
    end;
visit(_, _, Acc, T) -> {T, Acc}.

% The cells of a list after the first sit at the position of their element and are
% not expressions of their own.
-spec tail(fun((ast_erl:exp(), Acc) -> {ast_erl:exp(), Acc}), pos(), Acc, any()) -> {dynamic(), Acc}.
tail(F, Pos, Acc, {cons, A, H, T}) ->
    {H2, Acc1} = visit(F, Pos, Acc, H),
    {T2, Acc2} = tail(F, Pos, Acc1, T),
    {{cons, A, H2, T2}, Acc2};
tail(F, Pos, Acc, T) -> visit(F, Pos, Acc, T).

-spec is_expr(tuple()) -> boolean().
is_expr(T) ->
    tuple_size(T) >= 2 andalso
    lists:member(element(1, T),
                 [var, atom, integer, float, char, string, nil, cons, tuple, map, bin, call, op, match,
                  'case', 'if', 'receive', 'try', 'catch', 'fun', named_fun, block, lc, bc, mc, 'maybe']).
