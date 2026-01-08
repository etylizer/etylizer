%% Syntax elements for type annotations
%%
%% The macro ?annotate_type/2 can be used to annotate an expression with a type. 
%% This is useful to speed up type checking or as an assert that an expression should have the specified type. 
%% The specified type must be compatible with the type detected by Etylizer. Otherwise a type error is reported.
%%
%%     N = ?annotate_type( 10, non_neg_integer() )
%%
%% The macro ?assert_type/2 can be used to refine (downcast) a type propagated
%% by Etylizer. For example, the programmer may know that values stored in an ETS table
%% have a more precise type than term()
%%
%%     % MyETSValue :: term()
%%     Arity = ?assert_type( MyETSValue, {ok, any()} )
%%
%% The functions '::'/2 and ':::'/2 can also be used directly if the type is
%% quoted:
%%
%%     N = '::'(Message, "non_neg_integer()")
%%
%% Etylizer detects occurrences of the functions '::'/2 and ':::'/2 and
%% adjusts type checking accordingly. The macros are supplied only for
%% convenience.
%%
%% By default, Etylizer checks for exhaustiveness in expressions.
%% If you want to leverage the 'let it crash' behavior,
%% the pattern assertion macro can be used to force exhaustiveness of a pattern:
%%
%%     ?assert_pattern({ok, _}, file:read_file_info("myfile"))
%%
%% To bind the result to variables, match the entire macro result:
%%
%%     {ok, Info} = ?assert_pattern({ok, _}, file:read_file_info("myfile"))
%%
%% Note: Variables bound inside Pattern do not leak into the surrounding scope.
%% The macro uses a fun-call wrapper (IIFE) following the same convention as
%% OTP's assert.hrl to avoid exporting local variables.
%%
-compile({inline, ['::'/2, ':::'/2]}).
-compile({nowarn_unused_function, ['::'/2, ':::'/2]}).
-ignore_xref(['::'/2, ':::'/2]).

-spec '::'(A, _) -> A.
'::'(Expr, _Type) -> Expr.

-spec ':::'(A, _) -> A.
':::'(Expr, _Type) -> Expr.

%% Type annotation
-define(annotate_type(Expr, Type), '::'(Expr, ??Type)).

%% Type assertion
-define(assert_type(Expr, Type), ':::'(Expr, ??Type)).

%% Exhaustiveness cover to let it crash.
%% Uses a fun-call wrapper to avoid leaking the internal variable into the
%% surrounding scope. The X__V name follows OTP's assert.hrl convention.
-define(assert_pattern(Pattern, Expr),
    begin
    ((fun (X__V) ->
        case X__V of Pattern -> X__V; _ -> error(exhaustiveness_violated) end
      end)(Expr))
    end).
