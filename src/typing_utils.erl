-module(typing_utils).

-export([
    make_dynamic_fun_env/1
]).

%% @doc For a list of untyped function forms, generate a fun_env where each function
%% gets a type: (dynamic(),...,dynamic()) -> dynamic()
-spec make_dynamic_fun_env([ast:fun_decl()]) -> symtab:fun_env().
make_dynamic_fun_env(FunsWithoutSpec) ->
    maps:from_list([
        begin
            Args = lists:duplicate(Arity, {predef, dynamic}),
            Ref = {ref, Name, Arity},
            {Ref, {ty_scheme, [], {fun_full, Args, {predef, dynamic}}}}
        end || {function, _Loc, Name, Arity, _Clauses} <- FunsWithoutSpec
    ]).
