-module(parser_combinator).

% no helper functions, everything is exported
-compile([nowarn_export_all, export_all]).

-export_type([parser/1, lazy_parser/1, maybe_lazy_parser/1]).

-type lazy_parser(A) :: {lazy, fun(() -> parser(A))}.
-type parser(A) :: fun((string()) -> [{A, string()}]).
-type maybe_lazy_parser(A) :: lazy_parser(A) | parser(A).

-spec result(A) -> parser(A). 
result(V) -> fun(Input) -> [{V, Input}] end.

-spec zero() -> parser(_A). 
zero() -> fun(_Input) -> [] end.

-spec filter_unconsumed(parser(A)) -> parser(A).
filter_unconsumed(ParserA) ->
    fun(Input) ->
        [{Result, []} || {Result, []} <- ParserA(Input)]
    end.

-spec item() -> parser(char()). 
item() -> fun([]) -> []; ([X | Xs]) -> [{X, Xs}] end.

-spec bind(parser(A), fun((A) -> parser(B))) -> parser(B);
          (lazy_parser(A), fun((A) -> parser(B))) -> parser(B).
bind({lazy, ParserA}, Binder) -> bind(ParserA(), Binder);
bind(ParserA, Binder) ->
    fun(Input) -> 
        lists:flatten([(Binder(V))(InputPrime) || {V, InputPrime} <- ParserA(Input)])
    end.

-spec sat(fun((char()) -> boolean())) -> parser(char()).
sat(Predicate) ->
    bind(item(), fun(R) -> case Predicate(R) of true -> result(R); _ -> zero() end end).

-spec precedence_fun() -> parser(char()).
precedence_fun() -> char($o).

-spec char(char()) -> parser(char()).
char(C) -> sat(fun(R) -> R == C end).
-spec digit() -> parser(char()).
digit() -> sat(fun(C) -> C >= $0 andalso C =< $9 end).
-spec lower() -> parser(char()).
lower() -> sat(fun(C) -> C >= $a andalso C =< $z end).
-spec upper() -> parser(char()).
upper() -> sat(fun(C) -> C >= $A andalso C =< $Z end).

-spec plus(parser(A), parser(B)) -> parser(A | B).
plus(ParserA, ParserB) ->
    fun(Input) -> ParserA(Input) ++ ParserB(Input) end.

-spec choice([parser(A), ...]) -> parser(A).
choice(Parsers) ->
    fun(Input) -> lists:flatmap(fun(Parser) -> Parser(Input) end, Parsers) end.

-spec letter() -> parser(char()).
letter() -> plus(lower(), upper()).
-spec alphanum() -> parser(char()).
alphanum() -> plus(letter(), digit()).
-spec space() -> parser(char()).
space() -> sat(fun($ ) -> true;(_) -> false end).
-spec tabs() -> parser(char()).
tabs() -> sat(fun($\t) -> true;(_) -> false end).
-spec newline() -> parser(char()).
newline() -> sat(fun($\n) -> true;($\r) -> true;(_) -> false end).
-spec whitechar() -> parser(char()).
whitechar() -> plus(plus(space(), tabs()), newline()).

-spec take_right(parser(_A), parser(B)) -> parser(B). 
take_right(ParserA, ParserB) ->
    bind(ParserA, fun(_ResA) -> 
    bind(ParserB, fun(ResB) -> 
        result(ResB) 
    end) end).

-spec take_left(parser(A), parser(_B)) -> parser(A). 
take_left(ParserA, ParserB) ->
    bind(ParserA, fun(ResA) -> 
    bind(ParserB, fun(_ResB) -> 
        result(ResA) 
    end) end).

-spec optional(parser(A)) -> parser(none | A).
optional(ParserA) -> 
    optional_with(ParserA, none).

-spec optional_with(parser(A), With) -> parser(With | A).
optional_with(ParserA, With) -> 
  fun(Input) ->
      Res = ParserA(Input),
      case Res of
          [] -> (result(With))(Input);
          _ -> Res
      end
  end.
  
% multiple versions of less generic many_times
% -spec many_times(parser(char())) -> parser(string()).
% many_times(P) -> plus(bind(P, fun(Char) -> bind(many_times(P), fun(S) -> result([Char] ++ S) end) end), result("")).
% -spec many_times(parser(char()), string()) -> parser(string()).
% many_times(P, InitialValue) -> plus(bind(P, fun(Char) -> bind(many_times(P, InitialValue), fun(S) -> result([Char] ++ S) end) end), result(InitialValue)).
% -spec many_times(parser(char()), fun((char(), string()) -> string()), string()) -> parser(string()).
% many_times(P, Reducer, InitialValue) -> plus(bind(P, fun(Char) -> bind(many_times(P, Reducer, InitialValue), fun(S) -> result(Reducer(Char, S)) end) end), result(InitialValue)).

-spec many_times(parser(A), fun((A, B) -> B), B) -> parser(B).
many_times(P, Reducer, InitialValue) ->
    Seq = 
        bind(P, fun(A) -> 
        bind(many_times(P, Reducer, InitialValue), fun(S) -> 
            result(Reducer(A, S)) 
        end) end),
    plus(Seq, result(InitialValue)).

-spec many_times_string(parser(char())) -> parser(string()).
many_times_string(Parser) ->
    many_times(Parser, fun(Char, String) -> [Char] ++ String end, "").

-spec word() -> parser(string()).
word() ->
    many_times_string(letter()).

-spec remove_whitechar() -> parser(none | string()).
remove_whitechar() ->
    optional(many_times_string(whitechar())).

-spec single(parser(A)) -> parser(A).
single(Parser) -> 
    fun(Input) -> lists:sublist(Parser(Input), 1) end.

-spec seq(parser(A), parser([A])) -> parser([A]).
seq(Pa, Pb) ->
  bind(Pa, fun(Ra) -> 
  bind(Pb, fun(Rb) -> 
    result([Ra] ++ Rb)
           end) end).

-spec list_of(parser(A), parser(_B)) -> parser([A]).
list_of(Element, Separator) ->
  single(bind(optional(Element), fun(First) ->
    case First of
      none -> result([]);
      _ -> 
        seq(
          result(First),
          many_times(take_right(whitespace_around(Separator), Element), fun(Ele, Acc) -> [Ele] ++ Acc end, [])
         )
      end
  end)).

-spec around(parser(_), parser(A), parser(_)) -> parser(A).
around(Left, Parser, Right) ->
    take_left(
        take_right(Left, Parser),
        Right
    ).

-spec whitespace_around(parser(A)) -> parser(A).
whitespace_around(Parser) ->
    % TODO what effect does limiting the results to 1 have here?
    single(around(remove_whitechar(), Parser, remove_whitechar())).

-spec binary_operator(parser(A), parser(B), maybe_lazy_parser(C), fun((A,B,C) -> D)) -> parser(D).
binary_operator(Left, Op, Right, Reducer) ->
  bind(Left, fun(LeftRes) -> 
  bind(Op, fun(OpRes) -> 
  bind(Right, fun(RightRes) -> 
    result(Reducer(LeftRes, OpRes, RightRes))
  end) end) end).

-spec string(string()) -> parser(string()).
string([]) -> result("");
string([Char | Rest]) ->
  bind(char(Char), fun(C) -> 
  bind(string(Rest), fun(Str) -> 
    result([C] ++ Str)
  end) end).

-spec erlang_atom() -> parser(atom()).
erlang_atom() -> % a restricted version of the Erlang atom
    choice([
        around(string("'"), bind(word(), fun(Str) -> result(list_to_atom(Str)) end), string("'")),
        bind(lower(), fun(Start) -> bind(word(), fun(Rest) -> result(list_to_atom([Start] ++ Rest)) end) end)
    ]).

