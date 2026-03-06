-module(espresso_bin).
-export([get_path/0]).
-on_load(ensure_cached/0).

%% @doc Returns the path to the espresso binary in the user cache directory.
%% On module load, copies the binary from _build/espresso if not already cached.

-spec get_path() -> string().
get_path() ->
    filename:join(filename:basedir(user_cache, "etylizer"), "espresso").

%% Called via -on_load. OTP delays all calls to this module until
%% ensure_cached returns ok, so there is no race with get_path/0 callers.
-spec ensure_cached() -> ok.
ensure_cached() ->
    Path = get_path(),
    case filelib:is_regular(Path) of
        true -> ok;
        false ->
            filelib:ensure_dir(Path),
            {ok, _} = file:copy("_build/espresso", Path),
            ok = file:change_mode(Path, 8#755)
    end.
