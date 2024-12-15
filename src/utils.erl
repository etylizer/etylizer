-module(utils).

% @doc This module defines general purpose utility functions.

-include_lib("kernel/include/file.hrl").

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
-spec quit(non_neg_integer(), string(), [_]) -> ok.
quit(Code, Msg, L) ->
    io:format(Msg, L),
    halt(Code).

-spec quit(integer(), string()) -> ok.
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
replicate(_N, X) when X =< 0 -> [];
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
single(X) -> sets:from_list([X]).

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
