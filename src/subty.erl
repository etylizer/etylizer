-module(subty).

-export([
  is_subty/3,
  is_equivalent/3,
  is_any/2
]).

-ifdef(TEST).
-export([
  is_empty/2
]).
-endif.

is_equivalent(SymTab, S, T) -> is_subty(SymTab, S,T) andalso is_subty(SymTab, T,S).

-spec is_subty(symtab:t(), ast:ty(), ast:ty()) -> boolean().
is_subty(_Symtab, T1, T2) ->
  H1 = ty_parser:parse(T1),
  H2 = ty_parser:parse(T2),

  ty_node:leq(H1, H2).


is_any(T, Sym) ->
  is_subty(Sym, stdtypes:tany(), T).

-ifdef(TEST).
is_empty(T, Sym) ->
  is_subty(Sym, T, stdtypes:tnone()).
-endif.
