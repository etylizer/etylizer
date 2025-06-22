-module(utils).

% @doc This module defines general purpose utility functions.

-include_lib("kernel/include/file.hrl").
-include("log.hrl").

-export([
    quit/3, quit/2,
    everywhere/2, everything/2,
    error/2,
    is_string/1, is_char/1,
    sformat/2, sformat/3, sformat/4,  sformat/6, sformat/5, sformat/7, sformat1/2,
    if_true/2,
    file_get_lines/1, set_add_many/2, assert_no_error/1,
    replicate/2,
    string_ends_with/2, shorten/2,
    map_flip/2, foreach/2, concat_map/2,
    with_index/1, with_index/2,
    mkdirs/1, hash_sha1/1, hash_file/1,
    with_default/2, compare/2,
    timing/1,
    single/1,
    assocs_find/2, assocs_find_index/2,
    timeout/2, is_same_file/2, file_exists/1,
    normalize_path/1
]).

% quit exits the erlang program with the given exit code. No stack trace is produced,
% so don't use this function for aborting because of a bug.
-spec quit(non_neg_integer(), string(), [_]) -> _.
quit(Code, Msg, L) ->
    io:format(Msg, L),
    halt(Code).

-spec quit(non_neg_integer(), string()) -> _.
quit(Code, Msg) ->
    io:format(Msg),
    halt(Code).

-spec sformat_raw(string(), list()) -> string().
sformat_raw(Msg, L) ->
    lists:flatten(io_lib:format(Msg, L)).

% Does some magic to distinguish whether term() is a list of arguments or a single argument
-spec sformat(string(), term()) -> string().
sformat(Msg, []) ->
    % we dont know whether we have no argument or a single argument "".
    try sformat_raw(Msg, [])
    catch badarg:_:_ -> sformat_raw(Msg, [""])
    end;
sformat(Msg, X) ->
    L = case io_lib:char_list(X) of
            true -> [X]; % we have a single string argument
            false ->
                if
                    is_list(X) -> X; % we have a list of arguments
                    true -> [X]      % we have a single argument
                end
        end,
    sformat_raw(Msg, L).

-spec sformat1(string(), term()) -> string().
sformat1(Msg, X1) -> sformat_raw(Msg, [X1]).

-spec sformat(string(), term(), term()) -> string().
sformat(Msg, X1, X2) -> sformat_raw(Msg, [X1, X2]).

-spec sformat(string(), term(), term(), term()) -> string().
sformat(Msg, X1, X2, X3) -> sformat_raw(Msg, [X1, X2, X3]).

-spec sformat(string(), term(), term(), term(), term()) -> string().
sformat(Msg, X1, X2, X3, X4) -> sformat_raw(Msg, [X1, X2, X3, X4]).

-spec sformat(string(), term(), term(), term(), term(), term()) -> string().
sformat(Msg, X1, X2, X3, X4, X5) -> sformat_raw(Msg, [X1, X2, X3, X4, X5]).

-spec sformat(string(), term(), term(), term(), term(), term(), term()) -> string().
sformat(Msg, X1, X2, X3, X4, X5, X6) -> sformat_raw(Msg, [X1, X2, X3, X4, X5, X6]).

-spec error(string(), term()) -> no_return().
error(Msg, L) -> erlang:error(sformat(Msg, L)).

-spec is_string(term()) -> boolean().
is_string(X) -> io_lib:char_list(X).

-spec is_char(term()) -> boolean().
is_char(X) -> is_string([X]).

% Generically traverses the lists and tuples of a term
% and performs replacements as demanded by the given function.
% - If the function given returns {ok, X}, then the term is replaced
%   by X, no further recursive traversal is done.
% - If the function given returns {rec, X}, then the term is replaced
%   by X, and recursive traversal is done.
% - If the funtion returns error, then everywhere traverses the term recursively.
-spec everywhere(fun((term()) -> t:opt(term())), T) -> T.
everywhere(F, T) ->
    TransList = fun(L) -> lists:map(fun(X) -> everywhere(F, X) end, L) end,
    case F(T) of
        error ->
            case T of
                X when is_list(X) -> TransList(X);
                X when is_tuple(X) -> list_to_tuple(TransList(tuple_to_list(X)));
                X when is_map(X) -> maps:from_list(TransList(maps:to_list(X)));
                X -> X
            end;
        {ok, X} -> X;
        {rec, X} -> everywhere(F, X)
    end.

% Generically transforms the term given and collects all results T
% where the given function returns {ok, T} for a term. No recursive calls
% are made for such terms
-spec everything(fun((term()) -> t:opt(T)), term()) -> [T].
everything(F, T) ->
    TransList = fun(L) -> lists:flatmap(fun(X) -> everything(F, X) end, L) end,
    case F(T) of
        error ->
            case T of
                X when is_list(X) -> TransList(X);
                X when is_tuple(X) -> TransList(tuple_to_list(X));
                X when is_map(X) -> TransList(maps:to_list(X));
                _ -> []
            end;
        {ok, X} -> [X]
    end.

-spec if_true(boolean(), fun(() -> _T)) -> ok.
if_true(B, Action) ->
    if  B -> Action();
        true -> ok
    end,
    ok.

-spec file_get_lines(file:filename()) -> {ok, [string()]} | {error, _Why}.
file_get_lines(Path) ->
    case file:open(Path, [read]) of
        {error, X} -> {error, X};
        {ok, F} ->
            Get =
                fun Get(Acc) ->
                    case io:get_line(F, "") of
                        eof -> lists:reverse(Acc);
                        Line -> Get([Line | Acc])
                    end
                end,
            try {ok, Get([])} after file:close(F) end
    end.

-spec set_add_many([T], sets:set(T)) -> sets:set(T).
set_add_many(L, S) ->
    lists:foldl(fun sets:add_element/2, S, L).

-spec assert_no_error(T | error | {error, any()}) -> T.
assert_no_error(X) ->
    case X of
        error -> errors:bug("Did not expect an error");
        {error, _} -> errors:bug("Did not expect an error");
        _ -> X
    end.

-spec replicate(integer(), T) -> list(T).
replicate(N, _X) when N =< 0 -> [];
replicate(N, X) -> [X | replicate(N - 1, X)].

-spec string_ends_with(string(), string()) -> boolean().
string_ends_with(S, Suffix) ->
    string:find(S, Suffix, trailing) =:= Suffix.

-spec shorten(list(), integer()) -> {list(), integer()}.
shorten(L, N) when N < 0 -> {[], length(L)};
shorten([], _) -> {[], 0};
shorten([X | Xs], N) ->
    {Short, ShortN} = shorten(Xs, N - 1),
    {[X | Short], ShortN + 1}.

-spec map_flip([A], fun((A) -> B)) -> [B].
map_flip(L, F) -> lists:map(F, L).

-spec concat_map([A], fun((A) -> [B])) -> [B].
concat_map(L, F) -> lists:concat(lists:map(F, L)).

-spec foreach([T], fun((T) -> any())) -> ok.
foreach(L, F) -> lists:foreach(F, L).

-spec with_index([A]) -> [{integer(), A}].
with_index(L) -> with_index(0, L).

-spec with_index(integer(), [A]) -> [{integer(), A}].
with_index(Start, L) ->
    {_, Rev} = lists:foldl(fun (X, {I, Acc}) -> {I + 1, [{I, X} | Acc]} end,
                           {Start, []}, L),
    lists:reverse(Rev).

-spec mkdirs(file:filename()) -> ok | {error, string()}.
mkdirs(D) ->
    ok = filelib:ensure_dir(filename:join(D, "XXX")). % only creates the parent!

-spec hash_sha1(iodata()) -> string().
hash_sha1(Data) ->
    Digest = crypto:hash(sha, Data),
    Bin = binary:encode_hex(Digest),
    binary_to_list(Bin).

-spec hash_file(file:filename()) -> string() | {error, any()}.
hash_file(Path) ->
    case file:read_file(Path) of
        {ok, FileContent} -> utils:hash_sha1(FileContent);
        X -> X
    end.

-spec compare(integer(), integer()) -> less | equal | greater.
compare(I1, I2) ->
    case I1 < I2 of
        true -> less;
        false ->
            case I1 > I2 of
                true -> greater;
                false -> equal
            end
    end.

-spec with_default(T | undefined, T) -> T.
with_default(undefined, Def) -> Def;
with_default(X, _) -> X.

% Returns the time it takes to execute the given function in milliseconds
-spec timing(fun(() -> T)) -> {T, integer()}.
timing(F) ->
    Start = erlang:timestamp(),
    Res = F(),
    End = erlang:timestamp(),
    Delta = round(timer:now_diff(End, Start) / 1000),
    {Res, Delta}.

-spec single(T) -> sets:set(T).
single(X) -> sets:from_list([X], [{version, 2}]).

-spec assocs_find(K, [{K, V}]) -> {ok, V} | error.
assocs_find(K, L) ->
    case lists:keyfind(K, 1, L) of
        false -> error;
        {_Key, X} -> {ok, X}
    end.

-spec assocs_find_index(K, [{K, V}]) -> {ok, V, integer()} | error.
assocs_find_index(_, []) -> error;
assocs_find_index(K, [{K2, V} | _]) when K =:= K2 -> {ok, V, 0};
assocs_find_index(K, [_ | Rest]) ->
    case assocs_find_index(K, Rest) of
        {ok, V, I} -> {ok, V, I + 1};
        _ -> error
    end.

-spec timeout(integer(), fun(() -> T)) -> {ok, T} | timeout.
timeout(Millis, Fun) ->
    Self = self(),
    Pid = spawn(
      fun()->
          try
              X = Fun(),
              Self ! {ok, X}
          catch
              error:Reason -> Self ! {error, Reason};
              exit:_Reason -> ok;
              throw:Reason -> Self ! {throw, Reason}
          end
      end),
    receive
      {ok, Res} -> {ok, Res};
      {error, Reason} -> erlang:error(Reason);
      {throw, Reason} -> erlang:throw(Reason)
    after
       Millis ->
          exit(Pid, kill),
          timeout
    end.

is_same_file(Path1, Path2) ->
    case {file:read_file_info(Path1), file:read_file_info(Path2)} of
        {{ok, Info1}, {ok, Info2}} ->
            % Compare device and inode numbers
            Info1#file_info.type == Info2#file_info.type andalso
            Info1#file_info.major_device == Info2#file_info.major_device andalso
            Info1#file_info.inode == Info2#file_info.inode;
        _ ->
            % If either file does not exist or cannot be read, return false
            false
    end.

-spec file_exists(file:filename()) -> boolean().
file_exists(FilePath) ->
    case file:read_file_info(FilePath) of
        {ok, _Info} -> true;
        _ -> false
    end.

-spec normalize_path(file:filename()) -> file:filename().
normalize_path(P) ->
    case filename:nativename(P) of
        [ $. , $/ | Rest ] -> Rest;
        S -> S
    end.

-spec compare (fun((T, T) -> lt | gt | eq), [T], [T]) -> lt | gt | eq.
compare(_Cmp, [], []) -> eq;
compare(Cmp, [T1 | Ts1], [T2 | Ts2]) ->
  case Cmp(T1, T2) of
    eq -> compare(Cmp, Ts1, Ts2);
    R -> R
  end.

% -spec equal (fun((T, T) -> boolean()), [T], [T]) -> boolean().
% equal(_Eq, [], []) -> eg;
% equal(Eq, [T1 | Ts1], [T2 | Ts2]) ->
%   case Eq(T1, T2) of
%     true -> equal(Eq, Ts1, Ts2);
%     false -> false
%   end.

replace(Term, Mapping) ->
    replace_term(Term, Mapping).

replace_term({node, _} = Ref, Mapping) ->
    case maps:find(Ref, Mapping) of
        {ok, NewTerm} -> NewTerm;
        error -> Ref
    end;
replace_term({local_ref, _} = Ref, Mapping) ->
    case maps:find(Ref, Mapping) of
        {ok, NewTerm} -> NewTerm;
        error -> Ref
    end;
replace_term(Tuple, Mapping) when is_tuple(Tuple) ->
    list_to_tuple([replace_term(Element, Mapping) || Element <- tuple_to_list(Tuple)]);
replace_term([H|T], Mapping) ->
    [replace_term(H, Mapping) | replace_term(T, Mapping)];
replace_term(Map, Mapping) when is_map(Map) ->
    maps:from_list([{replace_term(K, Mapping), replace_term(V, Mapping)} || {K, V} <- maps:to_list(Map)]);
replace_term(Term, _Mapping) ->
    Term.

size(Term) ->
  (erts_debug:size(Term) * 8)/1024.

update_ets_from_map(EtsTable, LocalMap) ->
  % Filter LocalMap to only new/changed entries
  ChangedEntries = maps:fold(
      fun(K, V, Acc) ->
          case ets:lookup(EtsTable, K) of
              [{K, V}] -> Acc;
              _ -> [{K, V} | Acc]
          end
      end,
      [],
      LocalMap
  ),
  
  % Bulk-insert changes
  ets:insert(EtsTable, ChangedEntries).

map(Graph) ->
  All = lists:usort(lists:flatten([[K, V] || K := V <- Graph])),
  {Max, Mapping} = lists:foldl(fun(Node, {Id, Map}) -> {Id + 1, Map#{Node => Id}} end, {0, #{}}, All),
  Unfilled = #{maps:get(N, Mapping) => [maps:get(NN, Mapping) || NN <- Adj] || N := Adj <- Graph},
  {#{Id => maps:get(Id, Unfilled, []) || Id <- lists:seq(0, Max-1)}, Mapping}.


-spec condense(Graph) -> {SCCs, CondensedGraph} when
    Graph :: #{term() => [term()]},
    SCCs :: #{term() => term()},  % Maps each node to its root (SCC representative)
    CondensedGraph :: #{term() => [term()]}.  % Adjacency list of SCC roots
condense(Graph) ->
  {MappedGraph, Mapping} = map(Graph),
  IdNodeMapping = #{Id => Node || Node := Id <- Mapping},
  G = erlang:list_to_tuple([Adjacency || {_, Adjacency} <- lists:sort(maps:to_list(MappedGraph))]),
  {SCCs, Map} = tarjan:scc(G),

  ScctoN = #{Id => [maps:get(NN, IdNodeMapping) || NN <- Nodes] || {Id, Nodes} <- SCCs},
  NtoScc = #{maps:get(K, IdNodeMapping) => V || K := V <- Map},
  
  % Build a mapping from each node to its root (SCC representative)
  Roots = #{Node => hd(maps:get(Id, ScctoN)) || Node := Id <- NtoScc},
  
  % Get all unique SCC roots
  AllRoots = lists:usort(maps:values(Roots)),
  
  % Initialize the condensed graph with all roots (even those with no edges)
  BaseGraph = maps:from_list([{Root, []} || Root <- AllRoots]),
  
  % Build the condensed graph by:
  % 1. Collecting all edges between different SCCs
  % 2. Avoiding duplicate edges
  CondensedGraph = maps:fold(
      fun(Node, Neighbors, Acc) ->
          Root = maps:get(Node, Roots),
          lists:foldl(
              fun(Neighbor, InnerAcc) ->
                  NeighborRoot = maps:get(Neighbor, Roots),
                  case Root =/= NeighborRoot of
                      true ->
                          % Add edge from Root to NeighborRoot if not already present
                          CurrentEdges = maps:get(Root, InnerAcc),
                          case lists:member(NeighborRoot, CurrentEdges) of
                              false ->
                                  maps:put(Root, [NeighborRoot | CurrentEdges], InnerAcc);
                              true ->
                                  InnerAcc
                          end;
                      false ->
                          InnerAcc
                  end
              end,
              Acc,
              Neighbors
          )
      end,
      BaseGraph,  % Start with all roots already included
      Graph
  ),
  
  {Roots, CondensedGraph}.


dfs(Graph) ->
    Nodes = maps:keys(Graph),
    Visited = sets:new(),
    {Order, _} = lists:foldl(
        fun(Node, {Acc, VisitedSet}) ->
            case sets:is_element(Node, VisitedSet) of
                false ->
                    {NewAcc, NewVisited} = dfs_visit(Graph, Node, Acc, VisitedSet),
                    {NewAcc, NewVisited};
                true ->
                    {Acc, VisitedSet}
            end
        end,
        {[], Visited},
        Nodes
    ),
    lists:reverse(Order).

dfs_visit(Graph, Node, Acc, VisitedSet) ->
    NewVisited = sets:add_element(Node, VisitedSet),
    Neighbors = maps:get(Node, Graph, []),
    {NewAcc, FinalVisited} = lists:foldl(
        fun(Neighbor, {CurrentAcc, CurrentVisited}) ->
            case sets:is_element(Neighbor, CurrentVisited) of
                false ->
                    dfs_visit(Graph, Neighbor, CurrentAcc, CurrentVisited);
                true ->
                    {CurrentAcc, CurrentVisited}
            end
        end,
        {Acc, NewVisited},
        Neighbors
    ),
    {[Node | NewAcc], FinalVisited}.

revert_map(OriginalMap) ->
    maps:fold(fun(Key, Values, Acc) ->
        lists:foldl(fun(Value, InnerAcc) ->
            maps:put(Value, Key, InnerAcc)
        end, Acc, Values)
    end, #{}, OriginalMap).

reverse_graph(Graph) ->
    Keys = maps:keys(Graph),
    lists:foldl(
        fun(Key, Acc) ->
            case maps:get(Key, Graph) of
                [] -> Acc;  % No need to process nodes with no edges
                Values -> 
                    lists:foldl(
                        fun(Value, InnerAcc) ->
                            case maps:get(Value, InnerAcc, []) of
                                Existing -> InnerAcc#{Value => [Key | Existing]}
                            end
                        end,
                        Acc,
                        Values
                    )
            end
        end,
        #{K => [] || K <- Keys},  % Initialize with all keys pointing to empty lists
        Keys
    ).


map_with_context(Fun, List) ->
    map_with_context(Fun, List, []).

map_with_context(_Fun, [], Acc) ->
    lists:reverse(Acc);
map_with_context(Fun, [H|T], Acc) ->
    {Result, NewT} = Fun({H, T}),
    map_with_context(Fun, NewT, [Result|Acc]).


fold_with_context(_Fun, Acc, []) ->
    Acc;
fold_with_context(Fun, Acc, [H|T]) ->
    {NewAcc, NewT} = Fun({Acc, H, T}),
    fold_with_context(Fun, NewAcc, NewT).
