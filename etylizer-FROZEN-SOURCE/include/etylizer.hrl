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
%% To also bind the result to variables, match the entire macro:
%%
%%     {ok, Info} = ?assert_pattern({ok, _}, file:read_file_info("myfile"))
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

%% Exhaustiveness cover to let it crash
-define(assert_pattern(Pattern, Expr), case Expr of __Z = Pattern -> __Z; _ -> error(exhaustiveness_violated) end).
-define(assert_pattern(Pattern, Other, Expr), case Expr of Other = Pattern -> Other; _ -> error(exhaustiveness_violated) end).
