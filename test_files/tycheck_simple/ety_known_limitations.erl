-module(ety_known_limitations).

-compile(export_all).
-compile(nowarn_export_all).

% We intentionally have imprecise escape-variable handling.
%
% A variable created inside a case/if/receive branch and read after the construct is an escaping variable. 
% It is not given a precise type and instead is resolved as dynamic() (with a warning) at simplification time.
%
% That is imprecise, and it means these _fail cases no longer fail.
%
% 02-07-2026 albsch: 
%   Escape variables are very rare, and it is not worth the complexity inside the type checker to handle them properly
%   In ~200 out of 170000 functions escape variables are used where the precision could potentially matter (0.1%)
%   Properly handling it would mean one of those options:
%     1) annotate AST nodes which variables escape (initially tried in #326, but lead to bug #359)
%     2) thread through an environment just for variables from ast_transform through constr_gen
%     3) a let-normalization pass that rewrites expressions similar to what core erlang does
%        which is simple but makes comprehensions more expensive to type check as it introduces local functions
%
%   We already do a simplified version of 3) (shallow statement-level match nesting in ast_transform.erl) and
%   that is enough to cover most common cases.

-spec case_16_fail() -> ok.
case_16_fail() ->
    case ok of _ -> S = foo end,
    S.

-spec case_20_fail(foo | bar) -> foo | bar.
case_20_fail(X) ->
    case X of
        foo -> S = foo;
        bar -> S = fail
    end,
    S.

-spec case_21_fail(foo | bar) -> foo.
case_21_fail(X) ->
    case X of
        S when S == foo -> S;
        S when S == bar -> foo
    end,
    S.

-spec case_28_fail(foo | bar) -> bar.
case_28_fail(X) ->
    case X of
        S when {S, complex} == {foo, complex} -> S;
        S -> S
    end,
    S.

-spec case_30_fail(foo | bar) -> bar.
case_30_fail(X) ->
    case X of
        S when {foo, complex} == {S, complex} -> S;
        S -> S
    end,
    S.

-spec if_16_fail() -> ok.
if_16_fail() ->
    if true -> S = foo end,
    S.
