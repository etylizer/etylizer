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
is_subty(Symtab, T1, T2) ->
  H1 = ast_lib:ast_to_erlang_ty(T1, Symtab),
  H2 = ast_lib:ast_to_erlang_ty(T2, Symtab),

  ty_rec:is_subtype(H1, H2).


is_any(T, Sym) ->
  is_subty(Sym, stdtypes:tany(), T).

is_empty(T, Sym) ->
  is_subty(Sym, T, stdtypes:tnone()).
