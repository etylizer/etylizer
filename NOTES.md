# Extensions to erlang's type language

* ast_erl.erl defines several type synonyms for lists with a fixed number of
  elements in a fixed order, e.g. list1star(T, U) is a list with head T and
  tail [U]. Erlang's type syntax does not allow to express these types, so they
  are built from etylizer:cons(Head, Tail), the type of a single list cell.
  Other tools do not know this type.
