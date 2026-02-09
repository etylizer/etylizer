#!/usr/bin/env escript
%%! -noinput

main(_) ->
  {ok, [AllConstraints]} = file:consult("union.config"),

  App = fun(C) ->
    Get = fun ({var, A}) when is_atom(A) -> {ok, {var, A}}; (_) -> error end,
    everything(Get, C)
  end,
  
  VarGroups = [App(C) || C <- AllConstraints],




  io:format(user, "graph{~n", []),
  Z = fun(A) -> string:replace(atom_to_list(A), "$", "") end,
  Print = fun
    ([]) -> ok;
    ([_]) -> ok;
    (All) -> 
      [io:format(user,"  ~s -- ~s~n", [Z(R), Z(R2)]) || {var, R} <- All, {var, R2} <- All, R /= R2]
  end,
  
  lists:foreach(Print, VarGroups),
  io:format(user, "}~n", []),

  ok.


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
