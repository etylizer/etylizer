%%
%% %CopyrightBegin%
%% 
%% Copyright Ericsson AB 1996-2016. All Rights Reserved.
%% 
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%% 
%% %CopyrightEnd%
%%
-module(queue2).

%% Creation, inspection and conversion
-export([new/0,is_queue/1,is_empty/1,len/1,to_list/1,from_list/1,member/2]).
%% Original style API
-export([in/2,in_r/2,out/1,out_r/1]).
%% Less garbage style API
-export([get/1,get_r/1,peek/1,peek_r/1,drop/1,drop_r/1]).

%% Higher level API
-export([reverse/1,join/2,split/2,filter/2,filtermap/2,fold/3,any/2,all/2,
	 delete/2,delete_r/2,delete_with/2,delete_with_r/2]).

%% Okasaki API from klacke
-export([cons/2,head/1,tail/1,
	 snoc/2,last/1,daeh/1,init/1,liat/1]).

-export_type([queue/0, queue/1]).

%% Mis-spelled, deprecated.
-export([lait/1]).
-deprecated([{lait,1,"use queue:liat/1 instead"}]).

%%--------------------------------------------------------------------------
%% Efficient implementation of double ended fifo queues
%%
%% Queue representation
%%
%% {RearList,FrontList}
%%
%% The first element in the queue is at the head of the FrontList
%% The last element in the queue is at the head of the RearList,
%% that is; the RearList is reversed.
%%

-opaque queue(Item) :: {list(Item), list(Item)}.

-type queue() :: queue(_).

%% Creation, inspection and conversion

%% O(1)
-spec new() -> queue().
new() -> {[],[]}. %{RearList,FrontList}

%% O(1)
-spec is_queue(Term :: term()) -> boolean().
is_queue({R,F}) when is_list(R), is_list(F) ->
    true;
is_queue(_) ->
    false.

%% O(1)
-spec is_empty(Q :: queue()) -> boolean().
is_empty({[],[]}) ->
    true;
is_empty({In,Out}) when is_list(In), is_list(Out) ->
    false. 
% is_empty(Q) ->
%     erlang:error(badarg, [Q]).

%% O(len(Q))
-spec len(Q :: queue()) -> non_neg_integer().
len({R,F}) when is_list(R), is_list(F) ->
    length(R)+length(F).
% len(Q) ->
%     erlang:error(badarg, [Q]).

%% O(len(Q))
-spec to_list(Q :: queue(Item)) -> list(Item).
to_list({In,Out}) when is_list(In), is_list(Out) ->
    Out++lists:reverse(In, []).
% to_list(Q) ->
%     erlang:error(badarg, [Q]).

%% Create queue from list
%%
%% O(length(L))
-spec from_list(L :: list(Item)) -> queue(Item).
from_list(L) when is_list(L) ->
    f2r(L). %DIFF
% from_list(L) ->
%     erlang:error(badarg, [L]).

%% Return true or false depending on if element is in queue
%% 
%% O(length(Q)) worst case
-spec member(Item, Q :: queue(Item)) -> boolean().
member(X, {R,F}) when is_list(R), is_list(F) ->
    lists:member(X, R) orelse lists:member(X, F).
% member(X, Q) ->
%     erlang:error(badarg, [X,Q]).

%%--------------------------------------------------------------------------
%% Original style API

%% Append to tail/rear
%% Put at least one element in each list, if it is cheap
%%
%% O(1)
-spec in(Item, Q1 :: queue(Item)) -> Q2 :: queue(Item).
in(X, {[_]=In,[]}) ->
    {[X], In};
in(X, {In,Out}) when is_list(In), is_list(Out) ->
    {[X|In],Out}.
% in(X, Q) ->
%     erlang:error(badarg, [X,Q]).

%% Prepend to head/front
%% Put at least one element in each list, if it is cheap
%%
%% O(1)
-spec in_r(Item, Q1 :: queue(Item)) -> Q2 :: queue(Item).
in_r(X, {[],[_]=F}) ->
    {F,[X]};
in_r(X, {R,F}) when is_list(R), is_list(F) ->
    {R,[X|F]}.
% in_r(X, Q) ->
%     erlang:error(badarg, [X,Q]).

%% Take from head/front
%%
%% O(1) amortized, O(len(Q)) worst case
-spec out(Q1 :: queue(Item)) ->
                 {{value, Item}, Q2 :: queue(Item)} |
                 {empty, Q1 :: queue(Item)}.
out({[],[]}=Q) ->
    {empty,Q};
out({[V],[]}) ->
    {{value,V},{[],[]}};
out({[Y|In],[]}) ->
    [V|Out] = lists:reverse(In, []),
    {{value,V},{[Y],Out}};
out({In,[V]}) when is_list(In) ->
    {{value,V},r2f(In)};
out({In,[V|Out]}) when is_list(In) ->
    {{value,V},{In,Out}};
out(Q) ->
    erlang:error(badarg, [Q]).

%% Take from tail/rear
%%
%% O(1) amortized, O(len(Q)) worst case
-spec out_r(Q1 :: queue(Item)) ->
                 {{value, Item}, Q2 :: queue(Item)} |
                 {empty, Q1 :: queue(Item)}.
out_r({[],[]}=Q) ->
    {empty,Q};
out_r({[],[V]}) ->
    {{value,V},{[],[]}};
out_r({[],[Y|Out]}) ->
    [V|In] = lists:reverse(Out, []),
    {{value,V},{In,[Y]}};
out_r({[V],Out}) when is_list(Out) ->
    {{value,V},f2r(Out)};
out_r({[V|In],Out}) when is_list(Out) ->
    {{value,V},{In,Out}};
out_r(Q) ->
    erlang:error(badarg, [Q]).

%%--------------------------------------------------------------------------
%% Less garbage style API.

%% Return the first element in the queue
%%
%% O(1) since the queue is supposed to be well formed
-spec get(Q :: queue(Item)) -> Item.
get({[],[]}=Q) ->
    erlang:error(empty, [Q]);
get({R,F}) when is_list(R), is_list(F) ->
    get(R, F).
% get(Q) ->
%     erlang:error(badarg, [Q]).

% -spec get(list(), list()) -> term().
-spec get(list(Item), list(Item)) -> Item.
get([_ | R], _) -> lists:last(R);
get(_, _) -> error(todo).

%% Return the last element in the queue
%%
%% O(1) since the queue is supposed to be well formed
-spec get_r(Q :: queue(Item)) -> Item.
get_r({[],[]}=Q) ->
    erlang:error(empty, [Q]);
get_r({[H|_],F}) when is_list(F) ->
    H;
get_r({[],[H]}) ->
    H;
get_r({[],[_|F]}) -> % malformed queue -> O(len(Q))
    lists:last(F);
get_r(Q) ->
    erlang:error(badarg, [Q]).

%% Return the first element in the queue
%%
%% O(1) since the queue is supposed to be well formed
-spec peek(Q :: queue(Item)) -> empty | {value, Item}.
peek({[],[]}) ->
    empty;
peek({R,[H|_]}) when is_list(R) ->
    {value,H};
peek({[H],[]}) ->
    {value,H};
peek({[_|R],[]}) -> % malformed queue -> O(len(Q))
    {value,lists:last(R)};
peek(Q) ->
    erlang:error(badarg, [Q]).

%% Return the last element in the queue
%%
%% O(1) since the queue is supposed to be well formed
-spec peek_r(Q :: queue(Item)) -> empty | {value, Item}.
peek_r({[],[]}) ->
    empty;
peek_r({[H|_],F}) when is_list(F) ->
    {value,H};
peek_r({[],[H]}) ->
    {value,H};
peek_r({[],[_|R]}) -> % malformed queue -> O(len(Q))
    {value,lists:last(R)};
peek_r(Q) ->
    erlang:error(badarg, [Q]).

%% Remove the first element and return resulting queue
%%
%% O(1) amortized
-spec drop(Q1 :: queue(Item)) -> Q2 :: queue(Item).
drop({[],[]}=Q) ->
    erlang:error(empty, [Q]);
drop({[_],[]}) ->
    {[],[]};
drop({[Y|R],[]}) ->
    [_|F] = lists:reverse(R, []),
    {[Y],F};
drop({R, [_]}) when is_list(R) ->
    r2f(R);
drop({R, [_|F]}) when is_list(R) ->
    {R,F};
drop(Q) ->
    erlang:error(badarg, [Q]).

%% Remove the last element and return resulting queue
%%
%% O(1) amortized
-spec drop_r(Q1 :: queue(Item)) -> Q2 :: queue(Item).
drop_r({[],[]}=Q) ->
    erlang:error(empty, [Q]);
drop_r({[],[_]}) ->
    {[],[]};
drop_r({[],[Y|F]}) ->
    [_|R] = lists:reverse(F, []),
    {R,[Y]};
drop_r({[_], F}) when is_list(F) ->
    f2r(F);
drop_r({[_|R], F}) when is_list(F) ->
    {R,F};
drop_r(Q) ->
    erlang:error(badarg, [Q]).

%%--------------------------------------------------------------------------
%% Higher level API

%% Return reversed queue
%%
%% O(1)
-spec reverse(Q1 :: queue(Item)) -> Q2 :: queue(Item).
reverse({R,F}) when is_list(R), is_list(F) ->
    {F,R}.
% reverse(Q) ->
%     erlang:error(badarg, [Q]).

%% Join two queues
%%
%% Q2 empty: O(1)
%% else:     O(len(Q1))
-spec join(Q1 :: queue(Item), Q2 :: queue(Item)) -> Q3 :: queue(Item).
join({R,F}=Q, {[],[]}) when is_list(R), is_list(F) ->
    Q;
join({[],[]}, {R,F}=Q) when is_list(R), is_list(F) ->
    Q;
join({R1,F1}, {R2,F2}) when is_list(R1), is_list(F1), is_list(R2), is_list(F2) ->
    {R2,F1++lists:reverse(R1,F2)}.
% join(Q1, Q2) ->
%     erlang:error(badarg, [Q1,Q2]).

%% Split a queue in two
%%
%% N = 0..len(Q)
%% O(max(N, len(Q)))
-spec split(N :: non_neg_integer(), Q1 :: queue(Item)) ->
                   {Q2 :: queue(Item),Q3 :: queue(Item)}.
split(0, {R,F}=Q) when is_list(R), is_list(F) ->
    {{[],[]},Q};
split(N, {R,F}=Q) when is_integer(N), N >= 1, is_list(R), is_list(F) ->
    Lf = erlang:length(F),
    if  N < Lf -> % Lf >= 2
	    [X|F1] = F,
	    split_f1_to_r2(N-1, R, F1, [], [X]);
        N > Lf ->
	    Lr = length(R),
	    M = Lr - (N-Lf),
	    if  M < 0 ->
		    erlang:error(badarg, [N,Q]);
		M > 0 ->
		    [X|R1] = R,
		    split_r1_to_f2(M-1, R1, F, [X], []);
		true -> % M == 0
		    {Q,{[],[]}}
	    end;
	true -> % N == Lf
	    {f2r(F),r2f(R)}
    end;
split(N, Q) ->
    erlang:error(badarg, [N,Q]).

-spec split_f1_to_r2(integer(), [Item], [Item], [Item], [Item]) -> {queue(Item), queue(Item)}.
%% Move N elements from F1 to R2
split_f1_to_r2(0, R1, F1, R2, F2) ->
    {{R2,F2},{R1,F1}};
split_f1_to_r2(N, R1, [X|F1], R2, F2) ->
    split_f1_to_r2(N-1, R1, F1, [X|R2], F2).

-spec split_r1_to_f2(integer(), [Item], [Item], [Item],[Item]) -> {queue(Item), queue(Item)}.
%% Move N elements from R1 to F2
split_r1_to_f2(0, R1, F1, R2, F2) ->
    {{R1,F1},{R2,F2}};
split_r1_to_f2(N, [X|R1], F1, R2, F2) ->
    split_r1_to_f2(N-1, R1, F1, R2, [X|F2]).

%% filter, or rather filtermap with insert, traverses in queue order
%% 
%% Fun(_) -> List: O(length(List) * len(Q))
%% else:           O(len(Q)
-spec filter(Fun, Q1 :: queue(Item)) -> Q2 :: queue(Item) when
      Fun :: fun((Item) -> boolean() | list(Item)).
filter(Fun, {R0,F0}) when is_function(Fun, 1), is_list(R0), is_list(F0) ->
    F = filter_f(Fun, F0),
    R = filter_r(Fun, R0),
    if R =:= [] ->
	    f2r(F);
       F =:= [] ->
	    r2f(R);
       true ->
	    {R,F}
    end;
filter(Fun, Q) ->
    erlang:error(badarg, [Fun,Q]).

-spec filter_f(Fun, Q1 :: list(Item)) -> Q2 :: list(Item) when
      Fun :: fun((Item) -> boolean() | list(Item)).
%% Call Fun in head to tail order
filter_f(_, []) ->
    [];
filter_f(Fun, [X|F]) ->
    case Fun(X) of
	true ->
	    [X|filter_f(Fun, F)];
	[Y] ->
	    [Y|filter_f(Fun, F)];
	false ->
	    filter_f(Fun, F);
	[] ->
	    filter_f(Fun, F);
	L when is_list(L) ->
	    L++filter_f(Fun, F)
    end.

-spec filter_r(Fun, Q1 :: list(Item)) -> Q2 :: list(Item) when
      Fun :: fun((Item) -> boolean() | list(Item)).
%% Call Fun in reverse order, i.e tail to head
%% and reverse list result from fun to match queue order
filter_r(_, []) ->
    [];
filter_r(Fun, [X|R0]) ->
    R = filter_r(Fun, R0),
    case Fun(X) of
	true ->
	    [X|R];
	[Y] ->
	    [Y|R];
	false ->
	    R;
	[] ->
	    R;
	L when is_list(L) ->
	    lists:reverse(L, R)
    end.

%% Filter and map a queue, traverses in queue order.
%%
%% O(len(Q1))
-spec filtermap(Fun, Q1) -> Q2 when
      Fun :: fun((Item) -> boolean() | {'true', Value}),
      Q1 :: queue(Item),
      Q2 :: queue(Item | Value),
      Item :: term(),
      Value :: term().
filtermap(Fun, {R0, F0}) when is_function(Fun, 1), is_list(R0), is_list(F0) ->
    F = lists:filtermap(Fun, F0),
    R = filtermap_r(Fun, R0),
    if R =:= [] ->
	    f2r(F);
       F =:= [] ->
	    r2f(R);
       true ->
	    {R,F}
    end;
filtermap(Fun, Q) ->
    erlang:error(badarg, [Fun,Q]).

-spec filtermap_r(Fun, Q1) -> Q2 when
      Fun :: fun((Item) -> boolean() | {'true', Value}),
      Q1 :: list(Item),
      Q2 :: list(Item | Value),
      Item :: term(),
      Value :: term().
%% Call Fun in reverse order, i.e tail to head
filtermap_r(_, []) ->
    [];
filtermap_r(Fun, [X|R0]) ->
    R = filtermap_r(Fun, R0),
    case Fun(X) of
	true ->
	    [X|R];
	{true, Y} ->
	    [Y|R];
	false ->
	    R
    end.

%% Fold a function over a queue, in queue order.
%%
%% O(len(Q))
-spec fold(Fun, Acc0, Q :: queue(Item)) -> Acc1 when
      Fun :: fun((Item, AccIn) -> AccOut),
      Acc0 :: term(),
      Acc1 :: term(),
      AccIn :: term(),
      AccOut :: term().
fold(Fun, Acc0, {R, F}) when is_function(Fun, 2), is_list(R), is_list(F) ->
    Acc1 = lists:foldl(Fun, Acc0, F),
    lists:foldr(Fun, Acc1, R);
fold(Fun, Acc0, Q) ->
    erlang:error(badarg, [Fun, Acc0, Q]).

%% Check if any item satisfies the predicate, traverse in queue order.
%%
%% O(len(Q)) worst case
-spec any(Pred, Q :: queue(Item)) -> boolean() when
      Pred :: fun((Item) -> boolean()).
any(Pred, {R, F}) when is_function(Pred, 1), is_list(R), is_list(F) ->
    lists:any(Pred, F) orelse
    lists:any(Pred, R);
any(Pred, Q) ->
    erlang:error(badarg, [Pred, Q]).

%% Check if all items satisfy the predicate, traverse in queue order.
%%
%% O(len(Q)) worst case
-spec all(Pred, Q :: queue(Item)) -> boolean() when
      Pred :: fun((Item) -> boolean()).
all(Pred, {R, F}) when is_function(Pred, 1), is_list(R), is_list(F) ->
    lists:all(Pred, F) andalso
    lists:all(Pred, R);
all(Pred, Q) ->
    erlang:error(badarg, [Pred, Q]).

%% Delete the first occurence of an item in the queue,
%% according to queue order.
%%
%% O(len(Q1)) worst case
-spec delete(Item, Q1) -> Q2 when
      Item :: T,
      Q1 :: queue(T),
      Q2 :: queue(T),
      T :: term().
delete(Item, {R0, F0} = Q) when is_list(R0), is_list(F0) ->
    case delete_front(Item, F0) of
        false ->
            case delete_rear(Item, R0) of
                false ->
                    Q;
                [] ->
                    f2r(F0);
                R1 ->
                    {R1, F0}
            end;
        [] ->
            r2f(R0);
        F1 ->
            {R0, F1}
    end;
delete(Item, Q) ->
    erlang:error(badarg, [Item, Q]).

%% Delete the last occurence of an item in the queue,
%% according to queue order.
%%
%% O(len(Q1)) worst case
-spec delete_r(Item, Q1) -> Q2 when
      Item :: T,
      Q1 :: queue(T),
      Q2 :: queue(T),
      T :: term().
delete_r(Item, {R0, F0}) when is_list(R0), is_list(F0) ->
    {F1, R1}=delete(Item, {F0, R0}),
    {R1, F1}.
% delete_r(Item, Q) ->
%     erlang:error(badarg, [Item, Q]).

-spec delete_front(Item, [Item]) -> false | [Item].
delete_front(Item, [Item|Rest]) ->
    Rest;
delete_front(Item, [X|Rest]) ->
    case delete_front(Item, Rest) of
        false -> false;
        F -> [X|F]
    end;
delete_front(_, []) ->
    false.


-spec delete_rear(Item, [Item]) -> false | [Item].
delete_rear(Item, [X|Rest]) ->
    case delete_rear(Item, Rest) of
        false when X=:=Item ->
            Rest;
        false ->
            false;
        R ->
            [X|R]
    end;
delete_rear(_, []) ->
    false.

%% Delete the first occurence of an item in the queue
%% matching a predicate, according to queue order.
%%
%% O(len(Q1)) worst case
-spec delete_with(Pred, Q1) -> Q2 when
      Pred :: fun((Item) -> boolean()),
      Q1 :: queue(Item),
      Q2 :: queue(Item),
      Item :: term().
delete_with(Pred, {R0, F0} = Q) when is_function(Pred, 1), is_list(R0), is_list(F0) ->
    case delete_with_front(Pred, F0) of
	false ->
	    case delete_with_rear(Pred, R0) of
		false ->
		    Q;
		[] ->
		    f2r(F0);
		R1 ->
		    {R1, F0}
	    end;
	[] ->
	    r2f(R0);
	F1 ->
	    {R0, F1}
    end.
% delete_with(Pred, Q) ->
%     erlang:error(badarg, [Pred, Q]).

%% Delete the last occurence of an item in the queue
%% matching a predicate, according to queue order.
%%
%% O(len(Q1)) worst case
-spec delete_with_r(Pred, Q1) -> Q2 when
      Pred :: fun((Item) -> boolean()),
      Q1 :: queue(Item),
      Q2 :: queue(Item),
      Item :: term().
delete_with_r(Pred, {R0, F0}) when is_function(Pred, 1), is_list(R0), is_list(F0) ->
    {F1, R1} = delete_with(Pred, {F0, R0}),
    {R1, F1};
delete_with_r(Pred, Q) ->
    erlang:error(badarg, [Pred, Q]).

-spec delete_with_front(Pred, Q1) -> false | Q2 when
      Pred :: fun((Item) -> boolean()),
      Q1 :: [Item],
      Q2 :: [Item],
      Item :: term().
delete_with_front(Pred, [X|Rest]) ->
    case Pred(X) of
	true ->
	    Rest;
	false ->
	    case delete_with_front(Pred, Rest) of
		false ->
		    false;
		F ->
		    [X|F]
	    end
    end;
delete_with_front(_, []) ->
    false.

-spec delete_with_rear(Pred, R1) -> false | R2 when
      Pred :: fun((Item) -> boolean()),
      R1 :: [Item],
      R2 :: [Item],
      Item :: term().
delete_with_rear(Pred, [X|Rest]) ->
    case delete_with_rear(Pred, Rest) of
	false ->
	    case Pred(X) of
		true ->
		    Rest;
		false ->
		    false
	    end;
	R ->
	    [X|R]
    end;
delete_with_rear(_, []) ->
    false.

%%--------------------------------------------------------------------------
%% Okasaki API inspired by an Erlang user contribution "deque.erl" 
%% by Claes Wikstrom <klacke@kaja.klacke.net> 1999.
%%
%% This implementation does not use the internal data format from Klacke's
%% doubly ended queues that was "shamelessly stolen" from 
%% "Purely Functional Data structures" by Chris Okasaki, since the data
%% format of this module must remain the same in case some application
%% has saved a queue in external format or sends it to an old node.
%%
%% This implementation tries to do the best of the situation and should 
%% be almost as efficient as Okasaki's queues, except for len/1 that
%% is O(n) in this implementation instead of O(1).
%%
%% The new representation in this module again adds length field and
%% fixes this, but it is not yet default.
%%
%% The implementation keeps at least one element in both the forward
%% and the reversed lists to ensure that i.e head/1 or last/1 will
%% not have to reverse a list to find the element.
%%
%% To be compatible with the old version of this module, as much data as 
%% possible is moved to the receiving side using lists:reverse/2 when data
%% is needed, except for two elements (when possible). These two elements
%% are kept to prevent alternating tail/1 and init/1 operations from 
%% moving data back and forth between the sides.
%%
%% An alternative would be to balance for equal list length when one side
%% is exhausted. Although this could be better for a general double
%% ended queue, it would more han double the amortized cost for 
%% the normal case (one way queue).

%% Cons to head
%%
-spec cons(Item, Q1 :: queue(Item)) -> Q2 :: queue(Item).
cons(X, Q) ->
    in_r(X, Q).

%% Return head element
%%
%% Return the first element in the queue
%%
%% O(1) since the queue is supposed to be well formed
-spec head(Q :: queue(Item)) -> Item.
head({[],[]}=Q) ->
    erlang:error(empty, [Q]);
head({R,F}) when is_list(R), is_list(F) ->
    get(R, F).
% head(Q) ->
%     erlang:error(badarg, [Q]).

%% Remove head element and return resulting queue
%%
-spec tail(Q1 :: queue(Item)) -> Q2 :: queue(Item).
tail(Q) ->
    drop(Q).

%% Functions operating on the other end of the queue

%% Cons to tail
%%
-spec snoc(Q1 :: queue(Item), Item) -> Q2 :: queue(Item).
snoc(Q, X) ->
    in(X, Q).

%% Return last element
-spec daeh(Q :: queue(Item)) -> Item.
daeh(Q) -> get_r(Q).
-spec last(Q :: queue(Item)) -> Item.
last(Q) -> get_r(Q).

%% Remove last element and return resulting queue
-spec liat(Q1 :: queue(Item)) -> Q2 :: queue(Item).
liat(Q) -> drop_r(Q).
-spec lait(Q1 :: queue(Item)) -> Q2 :: queue(Item).
lait(Q) -> drop_r(Q). %% Oops, mis-spelled 'tail' reversed. Forget this one.
-spec init(Q1 :: queue(Item)) -> Q2 :: queue(Item).
init(Q) -> drop_r(Q).

%%--------------------------------------------------------------------------
%% Internal workers

-compile({inline, [{r2f,1},{f2r,1}]}).

-spec r2f([Item]) -> queue(Item).
%% Move half of elements from R to F, if there are at least three
r2f([]) ->
  erlang:'div'(1,2),
    {[],[]};
r2f([_]=R) ->
    {[],R};
r2f([X,Y]) ->
    {[X],[Y]};
r2f(List) ->
    {FF,RR} = lists:split(length(List) div 2 + 1, List),
    {FF,lists:reverse(RR, [])}.

%% Move half of elements from F to R, if there are enough
-spec f2r([Item]) -> queue(Item).
f2r([]) ->
    {[],[]};
f2r([_]=F) ->
    {F,[]};
f2r([X,Y]) ->
    {[Y],[X]};
f2r(List) ->
    {FF,RR} = lists:split(length(List) div 2 + 1, List),
    {lists:reverse(RR, []),FF}.
