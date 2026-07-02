-module(dynlang_pattern_examples).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

% all test cases from examples "Pattern Matching" from dynlang

-spec test_patterns({A, any()}) -> A.
test_patterns({A, _}) -> A.

-spec test2_patterns({B, A}) -> {B, A}.
test2_patterns(X) ->
    case X of 
        {A, _} ->
            case X of
                {_, B} -> {A, B}
            end
    end.



-spec pack(X, Y) ->{X, Y}.
pack(X, Y) -> {X, Y}.

-spec test3_patterns(A, B) -> {B, A}.
test3_patterns(X, Y) ->
    {Y2, X2} = pack(X, Y), % we don't have let bindings, new variable names
    pack(X2, Y2).

-spec typeof_patterns
(unit | []) -> string(); % -> "Nil"   % we don't have Strings as singletons
(string()) -> string();
(char()) -> string();
(integer()) -> string();
(boolean()) -> string();
(any()) -> string(). % we don't have negation to describe the last type without using e.g. etylizer:not
typeof_patterns(X) -> 
    case X of
        unit -> "Nil";
        [] -> "Nil";
        _ when is_list(X) -> "String"; % we don't have a string test in Erlang
        _ when is_integer(X) andalso X >= 0 andalso X =< 111411  -> "Char"; % we don't have a char test in Erlang
        _ when is_integer(X) -> "Number";
        _ when is_boolean(X) -> "Boolean";
        _ -> "Object"
    end.

% can't write this type properly:
%     (Any \ `true -> Any -> `false) 
%   & (`true       -> (`true -> `true) 
%   & (Any \ `true -> `false))  % TODO why is Any missing here?
-spec land_patterns(any(), any()) -> any().
land_patterns(A, B) -> 
    case {A, B} of
        {true, true} -> true; % we can't really match on types
        _ -> false
    end.

% fails
-spec fact
(0) -> 1; 
(neg_integer() | pos_integer()) -> integer().
fact(N) ->
    case N of
        0 -> 1;
        N -> (fact(N - 1)) * N
    end.

-spec succ(integer()) -> integer().
succ(N) -> N + 1.

-spec length([]) -> 0; (list()) -> integer().
length(Lst) ->
    case Lst of
        [] -> 0;
        [_| Tail] when is_list(Tail) -> succ(dynlang_examples:length(Tail))
    end.


% slightly different notation because we can't curry
-spec map
(fun((A) -> B) ,list(A)) -> list(B);
(fun((A) -> B) ,nonempty_list(A)) -> nonempty_list(B);
% (fun((A) -> B) ,[]) -> []; % we can't write this
(any() ,[]) -> [].
map(F, Lst) ->
    case Lst of
        [] -> 0;
        [E | InnerLst] when is_list(InnerLst)-> [(F(E)) | map(F, InnerLst)]
    end.


-spec map2(fun((A) -> B), list(A)) -> list(B).
map2(F, Lst) ->
    case Lst of
        [] -> 0;
        [E | InnerLst] -> [(F(E)) | map2(F, InnerLst)]
    end.

% ('b -> Any \ `true) & ('a -> Any) -> [ ('a | 'b)* ] -> [ ('a \ 'b)* ]
-spec filter(etylizer:intersection(fun((A) -> any()), fun((B) -> true)), list(A | B)) -> list(etylizer:without(A, B)).
filter(F, L) ->
    case L of
        [] -> [];
        [E | L_inner] ->
            case F(E) of
                true -> [E | filter(F, L_inner)];
                _ -> filter(F, L_inner)
            end
    end.

-type x1() :: {const, integer()} | {add, x1(), x1()} | {uminus, x1()}.
-spec eval({const, A}) -> A; (x1()) -> integer().
eval({add, E1, E2}) -> eval(E1) + eval(E2);
eval({uminus, E}) -> 0 - eval(E);
eval({const, X}) -> X.
    

-type expr() :: {const, non_neg_integer()} | {add, expr(), expr()} | {uminus, expr()}.
-spec eval_ann(expr()) -> integer().
eval_ann({add, E1, E2}) -> eval_ann(E1) + eval_ann(E2);
eval_ann({uminus, E}) -> 0 - eval_ann(E);
eval_ann({const, X}) -> X.