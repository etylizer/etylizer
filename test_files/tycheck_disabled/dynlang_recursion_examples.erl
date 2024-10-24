-module(dynlang_recursion_examples).

-compile(export_all).
-compile(nowarn_export_all).

% Each top-level definition of this module is typechecked in isolation
% against its spec, inference is also tested.
% If the name ends with _fail, the test must fail.

% all test cases from examples "Fixpoint & Recursion" from dynlang
% 
% (('a -> 'b) -> X1) -> X1 where X1 = ('a -> 'b) & 'c
% let fixpoint = fun f ->
%    let delta = fun x ->
%        f ( fun  v -> ( x x v ))
%      in delta delta
% 
% This is not the fixpoint in the dynlang example
% instead used Y & Z combinator examples:
% 
% ('a -> 'a) -> 'a
% let fix_y = fun f ->
%    (fun g -> f(g(g)))(fun g -> f(g(g)))
-spec fix_y(fun((A) -> A)) -> A.
fix_y(F) ->
    (fun(G) -> F(G(G)) end)(fun(G) -> F(G(G)) end).

% (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
% let fix = fun f ->
%    (fun g -> fun n -> (f(g(g)))(n))(fun g -> fun n -> (f(g(g)))(n))
-spec
fix(fun((fun((fun((A) -> B)) -> fun((A) -> B))) -> A)) -> B.
fix(F) ->
    (fun(G) -> fun(Lazy) -> (F(G(G)))(Lazy) end end)(fun(G) -> fun(Lazy) -> (F(G(G)))(Lazy) end end).
    

% we should be able to typecheck this
% TODO: Fails to type-check, why?
%   (Any -> 0 -> 1) 
% & 
%   ((Int -> Int) -> (*---1 | 1--* -> Int) & (0 -> 1))
-spec fact_gen
(any()                        ) -> fun((0) -> 1);
(fun((integer()) -> integer())) -> ety:intersection(
                                            fun((neg_integer() | pos_integer()) -> integer()), 
                                            fun((0) -> 1)
                                        ).
fact_gen(Fact) ->
    fun(0) -> 1;(N) -> Fact(N-1)*N end.


% This is OK though
-spec fact(0) -> 1;(neg_integer() | pos_integer()) -> integer().
fact(N) -> (fix(fun fact_gen/1))(N).


% TODO length_stub, length, map_stub, map, filter_stub, filter