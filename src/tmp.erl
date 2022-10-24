-module(tmp).

-export([
    with_tmp_file/4
    ]).

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
    Name = utils:sformat("~s~s-~s-~s~s", Prefix, int_to_hex(erlang:unique_integer([positive])),
            os:getpid(), int_to_hex(rand:uniform(100000000)), Suffix),
    filename:join(tmp_dir(), Name).

-spec with_tmp_file(string(), string(), delete | dont_delete,
    fun((file:io_device(), string()) -> T)) -> T.
with_tmp_file(Prefix, Suffix, Del, Action) ->
    P = tmp_filename(Prefix, Suffix),
    Modes = [exclusive],
    case file:open(P, Modes) of
        {ok, F} ->
            try Action(F, P)
            catch C:R:S ->
                file:close(F),
                utils:if_true(Del == delete, fun() -> file:delete(P) end),
                erlang:raise(C, R, S)
            end;
        {error, Reason} ->
            throw({error, utils:sformat("Error opening temporary file ~s with modes ~w: ~s",
                P, Modes, Reason)})
    end.
