%% Library specs for the riak_core_lite case study that overlay.erl does not have, or has for fewer
%% arguments. Each spec is true for every call of the function; none says more than the function does.
%% A result that OTP gives as a type variable bound only in `when` (which fits every type) is term() here.
-module(overlay_riak_core_lite_lib).
-compile(warn_missing_spec).
-compile([export_all, nowarn_export_all]).

%% ---------------------------------------------------------------------------------------------------
%% erlang

%% OTP: the result is a variable bound only in when
-spec 'erlang:hd'([T, ...]) -> T.
'erlang:hd'(_) -> error(overlay).

-spec 'erlang:tl'([T, ...]) -> [T].
'erlang:tl'(_) -> error(overlay).

%% OTP: max(Term1, Term2) -> Maximum, each of them a term()
-spec 'erlang:max'(A, B) -> A | B.
'erlang:max'(_, _) -> error(overlay).

-spec 'erlang:min'(A, B) -> A | B.
'erlang:min'(_, _) -> error(overlay).

%% OTP: get(Key) -> Val | undefined when Val :: term()
-spec 'erlang:get'(term()) -> term().
'erlang:get'(_) -> error(overlay).

%% a non-empty list has a positive length
-spec 'erlang:length'([term(), ...]) -> pos_integer(); ([term()]) -> non_neg_integer().
'erlang:length'(_) -> error(overlay).

%% the digits and the sign are bytes, OTP says string()
-spec 'erlang:integer_to_list'(integer()) -> [45 | 48..57, ...].
'erlang:integer_to_list'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% application

%% OTP: {ok, Val} when Val :: term()
-spec 'application:get_env'(atom(), atom()) -> undefined | {ok, term()}.
'application:get_env'(_, _) -> error(overlay).

%% OTP: Val when Val :: term()
-spec 'application:get_env'(atom(), atom(), term()) -> term().
'application:get_env'(_, _, _) -> error(overlay).

-spec 'application:get_key'(atom(), atom()) -> undefined | {ok, term()}.
'application:get_key'(_, _) -> error(overlay).

%% OTP: {error, Reason} when Reason :: term()
-spec 'application:start'(atom()) -> ok | {error, term()}.
'application:start'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% lists

%% OTP has five variables for the accumulator and the element, bound only in when
-spec 'lists:foldl'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldl'(_, _, _) -> error(overlay).

-spec 'lists:foldr'(fun((T, Acc) -> Acc), Acc, [T]) -> Acc.
'lists:foldr'(_, _, _) -> error(overlay).

-spec 'lists:mapfoldl'(fun((A, Acc) -> {B, Acc}), Acc, [A]) -> {[B], Acc}.
'lists:mapfoldl'(_, _, _) -> error(overlay).

%% OTP says tuple() for the elements of the key functions
-spec 'lists:keyfind'(term(), pos_integer(), [T]) -> T | false.
'lists:keyfind'(_, _, _) -> error(overlay).

-spec 'lists:keysearch'(term(), pos_integer(), [T]) -> {value, T} | false.
'lists:keysearch'(_, _, _) -> error(overlay).

-spec 'lists:keytake'(term(), pos_integer(), [T]) -> {value, T, [T]} | false.
'lists:keytake'(_, _, _) -> error(overlay).

-spec 'lists:keyreplace'(term(), pos_integer(), [T], New) -> [T | New].
'lists:keyreplace'(_, _, _, _) -> error(overlay).

-spec 'lists:keystore'(term(), pos_integer(), [T], New) -> [T | New, ...].
'lists:keystore'(_, _, _, _) -> error(overlay).

-spec 'lists:keydelete'(term(), pos_integer(), [T]) -> [T].
'lists:keydelete'(_, _, _) -> error(overlay).

-spec 'lists:keysort'(pos_integer(), [T]) -> [T].
'lists:keysort'(_, _) -> error(overlay).

-spec 'lists:ukeysort'(pos_integer(), [T]) -> [T].
'lists:ukeysort'(_, _) -> error(overlay).

-spec 'lists:ukeymerge'(pos_integer(), [A], [B]) -> [A | B].
'lists:ukeymerge'(_, _, _) -> error(overlay).

%% OTP: [integer()]. An ascending sequence does not go below its start.
-spec 'lists:seq'(pos_integer(), integer()) -> [pos_integer()];
                 (non_neg_integer(), integer()) -> [non_neg_integer()];
                 (integer(), integer()) -> [integer()].
'lists:seq'(_, _) -> error(overlay).

-spec 'lists:seq'(pos_integer(), integer(), pos_integer()) -> [pos_integer()];
                 (non_neg_integer(), integer(), pos_integer()) -> [non_neg_integer()];
                 (integer(), integer(), integer()) -> [integer()].
'lists:seq'(_, _, _) -> error(overlay).

%% OTP: number(). The sum of the empty list is 0, so a list of floats has to be non-empty for float().
-spec 'lists:sum'([non_neg_integer()]) -> non_neg_integer();
                 ([integer()]) -> integer();
                 ([float(), ...]) -> float();
                 ([number()]) -> number().
'lists:sum'(_) -> error(overlay).

%% OTP: [term()]. The elements of the result are the elements of the deep list that are not lists: for the
%% deep list of characters of io_lib, and for a list of elements and lists of elements when the elements
%% are no lists themselves. (A spec for every depth, deep(A) :: [A | deep(A)] with A without lists, runs
%% into the timeout of the checker in a comprehension and for an element type that is a type variable.)
-type deep_term() :: [term() | deep_term()].
-spec 'lists:flatten'(io_lib:chars()) -> string();
                     ([[etylizer:without(A, list())] | etylizer:without(A, list())]) -> [etylizer:without(A, list())];
                     (deep_term()) -> [term()].
'lists:flatten'(_) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% ordsets: OTP says ordset(_) for the results

-spec 'ordsets:subtract'([T], [term()]) -> [T].
'ordsets:subtract'(_, _) -> error(overlay).

-spec 'ordsets:intersection'([T], [term()]) -> [T].
'ordsets:intersection'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% dict: the parameters of dict:dict(K, V) do not appear in the definition of the type, a result of
%% type K or V fits every type. So the keys and values are term() here.

-spec 'dict:find'(term(), dict:dict()) -> {ok, term()} | error.
'dict:find'(_, _) -> error(overlay).

-spec 'dict:fetch'(term(), dict:dict()) -> term().
'dict:fetch'(_, _) -> error(overlay).

-spec 'dict:fetch_keys'(dict:dict()) -> [term()].
'dict:fetch_keys'(_) -> error(overlay).

-spec 'dict:to_list'(dict:dict()) -> [{term(), term()}].
'dict:to_list'(_) -> error(overlay).

-spec 'dict:fold'(fun((term(), term(), Acc) -> Acc), Acc, dict:dict()) -> Acc.
'dict:fold'(_, _, _) -> error(overlay).

-spec 'dict:merge'(fun((term(), term(), term()) -> term()), dict:dict(), dict:dict()) -> dict:dict().
'dict:merge'(_, _, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% crypto

%% OTP: binary() for every algorithm. A sha digest has 160 bits.
-spec 'crypto:hash'(sha, iodata()) -> <<_:160>>; (atom(), iodata()) -> binary().
'crypto:hash'(_, _) -> error(overlay).

%% ---------------------------------------------------------------------------------------------------
%% other modules


%% OTP: io_lib:latin1_string() and char(). Characters outside the letters of Latin-1 are left as they are.
-spec 'string:to_lower'(string()) -> string(); (char()) -> char().
'string:to_lower'(_) -> error(overlay).

%% OTP: file:filename_all(). The result is a binary only if an argument is one; for names that are
%% strings, atoms or deep lists it is a flat string.
-spec 'filename:join'(file:name(), file:name()) -> string();
                     (file:name_all(), file:name_all()) -> file:filename_all().
'filename:join'(_, _) -> error(overlay).
