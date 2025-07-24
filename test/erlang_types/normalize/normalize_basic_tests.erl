-module(normalize_basic_tests).

-include_lib("eunit/include/eunit.hrl").
-include_lib("test/erlang_types/erlang_types_test_utils.hrl").

basic_test() ->
  with_symtab(
    fun() -> 
      T1 = ty_parser:parse(tnamed(plus)),
      T2 = ty_parser:parse(tnamed(vars)),

      SnT1 = ty_node:difference(T1, T2),
      Norm = ty_node:normalize(SnT1, #{}),

      % solutions: variable 1 or 2 empty or int constraints on both variables
      3 = length(Norm),

      SnT2 = ty_parser:parse(tnamed(c1)),
      Norm2 = ty_node:normalize(SnT2, #{}),
      % single constraint
      1 = length(Norm2),

      % 1 constraint can be filtered (one variable cannot be empty anymore)
      Meet = constraint_set:meet(Norm, Norm2, #{}),
      2 = length(Meet),

      ok
    end, system("test_files/erlang_types/normalize/plus.config")).

queue_slow1_test_() ->
  {timeout, 50, fun() -> with_type(
    fun(Type) -> 
      FixedVariables = #{{var,name,'Item'} => [],{var,name,'Q1'} => [],{var,name,'Q2'} => []},
      {T, V} = timer:tc(fun() -> ty:normalize(Type, FixedVariables) end, millisecond),
      io:format(user,"~p ms~n~p~n", [T, length(V)]),
      19 = length(V),
      [{_, _, TyD}] = dnf_ty_variable:dnf(ty_node:load(Type)),
      {_, #{2 := Tup}} = ty_rec:pi(TyD, ty_tuples),
      Dnf = dnf_ty_tuple:dnf(Tup),
      io:format(user,"Dnf:~n~p~n", [length(Dnf)]),

      ok
    end, system("test_files/erlang_types/normalize/queue19.config")),

  with_type(
    fun(Type) -> 
      FixedVariables = #{{var,name,'Item'} => [],{var,name,'Q1'} => [],{var,name,'Q2'} => []},
      {T, V} = timer:tc(fun() -> ty:normalize(Type, FixedVariables) end, millisecond),
      io:format(user,"~p ms~n~p~n", [T, length(V)]),
      10 = length(V),
      [{_, _, TyD}] = dnf_ty_variable:dnf(ty_node:load(Type)),
      {_, #{2 := Tup}} = ty_rec:pi(TyD, ty_tuples),
      Dnf = dnf_ty_tuple:dnf(Tup),
      io:format(user,"Dnf:~n~p~n", [length(Dnf)]),
      ok
    end, system("test_files/erlang_types/normalize/queue10.config"))
                end }.





% 1. caching is not the problem
% just for debugging
% slow_test_() ->
%   {timeout, 45, fun() ->
%     with_type(
%       fun() -> 
%         Node = {node, 5165},
%         io:format(user,"Node: ~p~n", [Node]),
%         Empty = ty:is_empty(Node),
%         io:format(user,"Empty: ~p~n", [Empty]),
%         %Norm = ty:normalize(Node, #{}),
%
%         [{[], [], Ty}] = dnf_ty_variable:dnf(ty_node:load(Node)),
%         {{leaf, 0}, #{2 := Prod}} = ty_rec:pi(Ty, ty_tuples),
%         io:format(user, "Prod:~n~p~n", [Prod]),
%
%         Dnf = dnf_ty_tuple:dnf(Prod),
%         io:format(user, "Dnf:~n~p~n", [lists:usort(Dnf)]),
%
%         MergePos = [{merge(P), N, 1} || {P, N, 1} <- Dnf],
%         io:format(user, "Minimized:~n~p~n", [lists:usort(MergePos)]),
%
%
%         AllSingleNormalized = [
%                                begin {R, _} = dnf_ty_tuple:normalize_line(L, #{}, #{}), R end || L <- MergePos
%                               ],
%         io:format(user, "Normalized:~n~p~n", [AllSingleNormalized]),
%
%         Meet = constraint_set:meet(lists:nth(1, AllSingleNormalized), lists:nth(2, AllSingleNormalized), #{}),
%         io:format(user, "Meet1:~n~p~n", [Meet]),
%         Meet2 = constraint_set:meet(Meet, lists:nth(3, AllSingleNormalized), #{}),
%         io:format(user, "Meet2:~n~p~n", [Meet2]),
%         Meet3 = constraint_set:meet(Meet2, lists:nth(4, AllSingleNormalized), #{}),
%         io:format(user, "Meet3:~n~p~n", [Meet3]),
%
%         io:format(user, "Node:~n~p~n", [ty_node:dump({node, 5401})]),
%         io:format(user, "Node:~n~p~n", [ty_node:dump({node, 6101})]),
%
%         Z = lists:foldl(fun
%           (_Line, {[], ST0}) -> {[], ST0};
%           (R, CurrentConstr) -> 
%             io:format(user,"X", []),
%             constraint_set:meet(R, CurrentConstr, #{})
%         end, [[]], AllSingleNormalized),
%
%         ok
%       end, system("test_files/erlang_types/types/slow.type"))
%   end}.
%
% merge(L) ->
%   % io:format(user,"Merging: ~p~n", [L]),
%   P = {ty_tuple, 2, [A, _B]} = ty_tuple:big_intersect(L),
%   io:format(user,"Got: ~p~n", [ty_node:dump(A)]),
%   [P].


