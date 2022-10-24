-module(pp).

% @doc Pretty-printing functions. For ast nodes, the function for pretty-printing
% has the same name as the ast type.

-export([
    global_ref/1
]).

-spec global_ref(ast:global_ref()) -> string().
global_ref(Ref) ->
    case Ref of
      {ref, Name, Arity} -> utils:sformat("~w/~w", Name, Arity);
      {qref, Mod, Name, Arity} -> utils:sformat("~w:~w/~w", Mod, Name, Arity)
    end.