-module(tmp).

-include("log.hrl").

-export([
    with_tmp_file/4
    ]).

-ifdef(TEST).
-export([
    with_tmp_dir/4
   ]).
-endif.

-spec int_to_hex(integer()) -> string().
int_to_hex(I) -> integer_to_list(I, 16).

-spec tmp_dir() -> string().
tmp_dir() ->
    F =
        fun F([]) -> ".";
            F([V | Vs]) ->
                case os:getenv(V) of
                    false -> F(Vs);
                    X -> X
                end
    end,
    F(["TMPDIR", "TEMP", "TMP"]).

-spec tmp_filename(string(), string()) -> string().
tmp_filename(Prefix, Suffix) ->
    Clean = fun(S) -> string:replace(S, "/", "_", all) end,
    Name = utils:sformat("~s~s-~s-~s~s", Clean(Prefix), int_to_hex(erlang:unique_integer([positive])),
            os:getpid(), int_to_hex(rand:uniform(100000000)), Clean(Suffix)),
    filename:join(tmp_dir(), Name).

-spec with_tmp_file(string(), string(), delete | dont_delete,
    fun((file:io_device(), string()) -> T)) -> T.
with_tmp_file(Prefix, Suffix, Del, Action) ->
    P = tmp_filename(Prefix, Suffix),
    Modes = [exclusive],
    case file:open(P, Modes) of
        {ok, F} ->
            try Action(F, P)
            after
                file:close(F),
                utils:if_true(Del == delete, fun() -> file:delete(P) end)
            end;
        {error, Reason} ->
            throw({error, utils:sformat("Error opening temporary file ~s with modes ~w: ~s",
                P, Modes, Reason)})
    end.

-spec with_tmp_dir(string(), string(), delete | dont_delete,
    fun((string()) -> T)) -> T.
with_tmp_dir(Prefix, Suffix, Del, Action) ->
    P = tmp_filename(Prefix, Suffix),
    ?LOG_INFO("Creating temporary directory ~p", P),
    utils:mkdirs(P),
    try Action(P)
    after
        utils:if_true(Del == delete,
            fun() ->
                ?LOG_NOTE("Removing temporary directory ~p", P),
                os:cmd("rm -Rf " ++ P)
            end)
    end.
