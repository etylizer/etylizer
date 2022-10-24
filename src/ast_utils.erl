-module(ast_utils).

-export([remove_locs/1]).

-spec remove_locs(T) -> T.
remove_locs(X) ->
    LocToError = fun(Z) ->
        case Z of
            {loc, _, _, _} -> {ok, {loc, "", 0, 0}};
            _ -> error
        end
    end,
    utils:everywhere(LocToError, X).
