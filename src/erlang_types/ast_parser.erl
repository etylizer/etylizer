-module(ast_parser).


-export([parse_command/1, parse_type/1, parse_type_definition/1]).

-export_type([
              command_tally_satisfiability/0,
              command_equal/0,
              command_type/0,
              command_type_definition/0,
              command_subtype/0
             ]).

-include("parser_combinator_import.hrl").
-include("etylizer.hrl").


-type parser(A) :: parser_combinator:parser(A).
-define(LAZY(F), {lazy, fun() -> F end}).

-type commands() ::  command_tally_satisfiability() 
                   | command_type() 
                   | command_type_definition() 
                   | command_subtype() 
                   | command_equal().

-type command_tally_satisfiability() :: {tally_satisfiability, [{ast:ty(), ast:ty()}]}.
-type command_type() :: {type, ast:ty()}.
-type command_type_definition() :: {type_definition, ast:tydef()}.
-type command_equal() :: {equal, ast:ty(), ast:ty()}.
-type command_subtype() :: {subtype, ast:ty(), ast:ty()}.

-spec parse_command(string()) -> {ok, commands()} | error.
parse_command(String) ->
    consume_all_or_error(fun parse_all/0, String).

% type atom()(args*) = ty().
-spec parse_type_definition(string()) -> error | {ok, ast:tydef()}.
parse_type_definition(String) ->
    consume_all_or_error(fun type_definition/0, String).

-spec parse_type(string()) -> error | {ok, ast:ty()}.
parse_type(String) ->
    consume_all_or_error(fun ty/0, String).

-spec consume_all_or_error(fun(() -> parser(A)), string()) -> error | {ok, A}.
consume_all_or_error(F, Input) ->
    case (F())(Input) of
        [] -> error;
        [{Result, []} | _] -> {ok, Result};
        _ -> error
    end.

-spec parse_all() -> parser(commands()).
parse_all() ->
    choice( [
        ?annotate_type(bind(filter_unconsumed(whitespace_around(tally_satisfiability())), fun({tally_satisfiability, ListOfTys}) -> result({tally_satisfiability, ListOfTys}) end), parser(command_tally_satisfiability())),
        ?annotate_type(bind(filter_unconsumed(subtype_check()), fun({subtype, Ty1, Ty2}) -> result({subtype, Ty1, Ty2}) end), parser(command_subtype())),
        ?annotate_type(bind(filter_unconsumed(binary_operator(ty(), whitespace_around(string(">=")), ty(), fun(Ty1,_,Ty2) -> {Ty1, Ty2} end)), fun({Ty1, Ty2}) -> result({subtype, Ty2, Ty1}) end), parser(command_subtype())),
        ?annotate_type(bind(filter_unconsumed(binary_operator(ty(), whitespace_around(string("=")), ty(), fun(Ty1,_,Ty2) -> {Ty1, Ty2} end)), fun({Ty1, Ty2}) -> result({equal, Ty2, Ty1}) end), parser(command_equal())),
        ?annotate_type(bind(filter_unconsumed(ty()), fun(T) -> result({type, T}) end), parser(command_type())),
        ?annotate_type(bind(filter_unconsumed(type_definition()), fun(T) -> result({type_definition, T}) end), parser(command_type_definition()))
    ]).

% ty() <= ty()
-spec subtype_check() -> parser({subtype, ast:ty(), ast:ty()}).
subtype_check() ->
    binary_operator(ty(), whitespace_around(string("<=")), ty(), fun(Ty1,_,Ty2) -> {subtype, Ty1, Ty2} end).

% ?[ ty* ]
-spec tally_satisfiability() -> parser(command_tally_satisfiability()).
tally_satisfiability() ->
    bind(string("?["), fun(_) ->
    bind(list_of(subtype_check(), string(";")), fun(ListOfTys) ->
    bind(string("]"), fun(_) ->
        result({tally_satisfiability, [{T1, T2} || {subtype, T1, T2} <- ListOfTys]})
    end) end) end).

% TODO parse bounded vars
-spec type_definition() -> parser(ast:tydef()).
type_definition() ->
    bind(string("type"), fun(_) ->
    bind(whitespace_around(erlang_atom()), fun(TypeName) ->
    bind(whitespace_around(string("()")), fun(_) -> 
    bind(whitespace_around(string("=")), fun(_) -> 
    bind(ty(), fun(Ty) -> 
        result({TypeName, {ty_scheme, [], Ty}})
    end) end) end) end) end).

-spec ty_singleton() -> parser(ast:ty_singleton()).
ty_singleton() -> 
    choice([
        bind(erlang_atom(), fun(Atom) -> result({singleton, Atom}) end)
    ]).

-spec ty_bitstring() -> parser(ast:ty_bitstring()).
ty_bitstring() -> zero(). % TODO

-spec ty_some_list() -> parser(ast:ty_some_list()).
ty_some_list() -> zero(). % TODO

-spec ty_integer_range() -> parser(ast:ty_integer_range()).
ty_integer_range() -> zero(). % TODO

-spec ty_map_any() -> parser(ast:ty_map_any()).
ty_map_any() -> zero(). % TODO

-spec ty_map() -> parser(ast:ty_map()).
ty_map() -> zero(). % TODO

-spec ty_predef() -> parser(ast:ty_predef()).
ty_predef() -> 
    bind(whitespace_around(erlang_atom()), fun(Name) ->
        case ast:maybe_predef_name(Name) of
            {true, Predef} -> bind(string("()"), fun(_) -> 
                        result({predef, Predef})
                                       end);
            false -> zero()
        end
    end).

-spec ty_predef_alias() -> parser(ast:ty_predef_alias()).
ty_predef_alias() -> zero(). % TODO

-spec ty_named() -> parser(ast:ty_named()).
ty_named() -> zero(). % TODO

-spec ty_tuple_any() -> parser(ast:ty_tuple_any()).
ty_tuple_any() -> zero(). % TODO

-spec ty_tuple() -> parser(ast:ty_tuple()).
ty_tuple() -> 
    bind(char(${), fun(_) ->
    bind(whitespace_around(list_of_tys()), fun(Tys) ->
    bind(char($}), fun(_) ->
        result({tuple, Tys})
    end) end) end).

-spec ty_var() -> parser(ast:ty_var()).
ty_var() -> choice([polymorphic_variable(), monomorphic_variable()]). 

-spec ty_mu_var() -> parser(ast:ty_mu_var()).
ty_mu_var() -> zero(). % TODO

-spec ty_mu() -> parser(ast:ty_mu()).
ty_mu() -> zero(). % TODO

-spec ty_fun() -> parser(ast:ty_fun()).
ty_fun() ->
    binary_operator(
        ty_tuple(), 
        whitespace_around(string("->")), 
        ?LAZY(precedence_fun()), 
        fun({tuple, Domain}, _, Codomain) -> {fun_full, Domain, Codomain} end
    ).

-spec ty_union() -> parser(ast:ty_union()).
ty_union() -> 
    binary_operator(
        precedence_intersection(), 
        whitespace_around(string("|")), 
        ?LAZY(precedence_union()), 
        fun(Ty1, _, Ty2) -> {union, [Ty1, Ty2]} end
    ).

-spec ty_intersection() -> parser(ast:ty_intersection()).
ty_intersection() -> 
    binary_operator(
        precedence_difference(), 
        whitespace_around(string("&")), 
        ?LAZY(precedence_intersection()), 
        fun(Ty1, _, Ty2) -> {intersection, [Ty1, Ty2]} end
    ).

-spec ty_difference() -> parser(ast:ty_intersection()). % there is no difference
ty_difference() -> 
    binary_operator(
        precedence_negation(), 
        whitespace_around(string("\\")), 
        ?LAZY(precedence_difference()), 
        ?annotate_type(
           fun(Ty1, _, Ty2) -> {intersection, [Ty1, {negation, Ty2}]} end, 
           fun((ast:ty(), _, ast:ty()) -> ast:ty_intersection())
           )
    ).


-spec ty_negation() -> parser(ast:ty_negation()).
ty_negation() -> 
    bind(char($!), fun(_) -> 
    bind(precedence_negation(), fun(Ty) -> 
        result({negation, Ty})
    end) end).

-spec simple_ty() -> parser(ast:ty()).
simple_ty() ->
    whitespace_around(
        choice([
            ty_singleton(),
            ty_bitstring(),
            ty_some_list(),
            ty_integer_range(),
            ty_map_any(),
            ty_map(),
            ty_predef(),
            ty_predef_alias(),
            ty_named(),
            ty_tuple_any(),
            ty_tuple(),
            ty_var(),
            ty_mu_var(),
            ty_mu()
    ])).


-spec variable(parser(char())) -> parser(ast:ty_var()).
variable(Mode) ->
    bind(char($'), fun(_) ->
    bind(Mode, fun(First) ->
    bind(many_times_string(alphanum()), fun(Rest) ->
        result({var, list_to_atom([First] ++ Rest)})
    end) end) end).


% 'Xa1
-spec polymorphic_variable() -> parser(ast:ty_var()).
polymorphic_variable() -> variable(upper()).

% 'xa1
-spec monomorphic_variable() -> parser(ast:ty_var()).
monomorphic_variable() -> variable(lower()).

% ty? (,ty)*
-spec list_of_tys() -> parser([ast:ty()]).
list_of_tys() ->
    list_of(ty(), char($,)).

-spec ty_with_parenthesis() -> parser(ast:ty()).
ty_with_parenthesis() -> 
    bind(char($(), fun(_) -> 
    bind(ty(), fun(Ty) -> 
    bind(char($)), fun(_) -> 
        result(Ty)
    end) end) end).

-spec ty() -> parser(ast:ty()).
ty() -> precedence_fun().

% precedence ladder
-spec precedence_fun() -> parser(ast:ty()).
precedence_fun() -> plus(ty_fun(), precedence_union()).

-spec precedence_union() -> parser(ast:ty()).
precedence_union() -> plus(ty_union(), precedence_intersection()).

-spec precedence_intersection() -> parser(ast:ty()).
precedence_intersection() -> plus(ty_intersection(), precedence_difference()).

-spec precedence_difference() -> parser(ast:ty()).
precedence_difference() -> plus(ty_difference(), precedence_negation()).

-spec precedence_negation() -> parser(ast:ty()).
precedence_negation() -> plus(ty_negation(), precedence_ty()).

-spec precedence_ty() -> parser(ast:ty()).
precedence_ty() -> plus(ty_with_parenthesis(), simple_ty()).

