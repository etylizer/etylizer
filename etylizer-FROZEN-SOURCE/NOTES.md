# Extensions to erlang's type language

* ast_erl.erl defines several type synonyms for better type lists, e.g.
  list1star(T, U) is a list with head T and tail [U]. However, erlang's
  type syntax does not allow to express this type precisly.
