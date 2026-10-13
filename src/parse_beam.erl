-module(parse_beam).

% extracts Erlang abstract forms from compiled BEAM files

-export([parse_beam_file/1]).

-ifdef(TEST).
-export([default_arg_specs/1]).
-endif.

-include("log.hrl").
-include("etylizer.hrl").

% beam_lib reads the forms with the backend named in the debug_info chunk
-spec parse_beam_file(file:filename()) -> {ok, [ast_erl:form()]} | error.
parse_beam_file(Path) ->
    case beam_lib:chunks(Path, [debug_info, abstract_code]) of
        {ok, {_, [{debug_info, {debug_info_v1, elixir_erl, _}}, {abstract_code, {raw_abstract_v1, Forms}}]}} ->
            {ok, default_arg_specs(filter_elixir_generated(Forms))};
        {ok, {_, [_, {abstract_code, {raw_abstract_v1, Forms}}]}} ->
            {ok, Forms};
        {ok, {_, [_, {abstract_code, no_abstract_code}]}} ->
            ?LOG_ERROR("No debug_info in BEAM file ~s. Compile with debug_info enabled.", Path),
            error;
        {error, beam_lib, {missing_backend, _, Backend}} ->
            ?LOG_ERROR("The debug_info of ~s is read with module ~w, which is not on the code path. "
                "Add its directory with --pa.", Path, Backend),
            error;
        {error, beam_lib, Reason} ->
            ?LOG_ERROR("Failed to read BEAM file ~s: ~p", Path, Reason),
            error
    end.

% Filter out Elixir auto-generated functions that have no spec (e.g. __info__/1).
-spec filter_elixir_generated([ast_erl:form()]) -> [ast_erl:form()].
filter_elixir_generated(Forms) ->
    lists:filter(fun(Form) ->
        case Form of
            {function, _, '__info__', 1, _} -> false;
            _ -> true
        end
    end, Forms).

% Elixir compiles `def f(a, b \\ 1, c)` to f/3 and to a wrapper without spec:
% f(X1, X2) -> f(X1, 1, X2). An exported wrapper gets the spec of f/3, reduced to the
% parameters it passes on.
-spec default_arg_specs([ast_erl:form()]) -> [ast_erl:form()].
default_arg_specs(Forms) ->
    Exports = [F || {attribute, _, export, Fs} <- Forms, F <- ?assert_type(Fs, [ast_erl:fun_with_arity()])],
    Specs = maps:from_list(
        [?assert_type(S, {ast_erl:fun_with_arity(), [ast_erl:ty_full_fun()]}) || {attribute, _, spec, S} <- Forms]),
    Forms ++ lists:filtermap(
        fun({function, Anno, Name, Arity, [Clause]}) ->
                Fun = {Name, Arity},
                case lists:member(Fun, Exports) andalso not maps:is_key(Fun, Specs) of
                    true -> wrapper_spec(Anno, Fun, passed_on(Name, Clause), Specs);
                    false -> false
                end;
           (_) -> false
        end, Forms).

% For a clause f(X1, ..., Xn) -> f(...) that passes every Xi on exactly once: where
% each Xi is in the call, and the number of arguments of the call.
-spec passed_on(atom(), ast_erl:fun_clause()) -> {ok, [pos_integer()], integer()} | error.
passed_on(Name, {clause, _, Params, [], [{call, _, {atom, _, Name}, Args}]})
  when length(Args) > length(Params) ->
    Positions = [[I || {I, {var, _, A}} <- lists:enumerate(Args), A =:= X] || {var, _, X} <- Params],
    case length(Positions) =:= length(Params) andalso lists:all(fun(P) -> length(P) =:= 1 end, Positions) of
        true -> {ok, ?assert_type(lists:append(Positions), [pos_integer()]), length(Args)};
        false -> error
    end;
passed_on(_, _) -> error.

% No spec if the called function has none or one with constraints.
-spec wrapper_spec(ast_erl:anno(), ast_erl:fun_with_arity(), {ok, [pos_integer()], integer()} | error,
    #{ast_erl:fun_with_arity() => [ast_erl:ty_full_fun()]}) -> {true, ast_erl:form()} | false.
wrapper_spec(Anno, Fun = {Name, _}, {ok, Positions, CallArity}, Specs) ->
    Tys = maps:get({Name, CallArity}, Specs, []),
    Reduced = [{type, A, 'fun', [{type, PA, product, [lists:nth(P, Params) || P <- Positions]}, Ret]}
               || {type, A, 'fun', [{type, PA, product, Params}, Ret]} <- Tys],
    case Tys =/= [] andalso length(Reduced) =:= length(Tys) of
        true -> {true, {attribute, Anno, spec, {Fun, Reduced}}};
        false -> false
    end;
wrapper_spec(_, _, error, _) -> false.
